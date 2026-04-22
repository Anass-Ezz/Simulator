"""
Socomec Digiware I60 Meter Simulator v4
Simulates complete I60/I30/I35 meters (each with load slots) over Modbus TCP

Register encoding — derived from the Java OpenEMS polling code:

  VOLTAGE  (L1/L2/L3)  → SCALE_FACTOR_MINUS_2  → channel MILLIVOLT
      raw × 10⁻² = V  →  raw × 10⁻² × 1000 = mV
      ∴  raw = V × 100  (centivolt, cV)
      e.g. 230.0 V → raw = 23 000

  CURRENT  (I1/I2/I3)  → SCALE_FACTOR_MINUS_3  → channel MILLIAMPERE
      raw × 10⁻³ = A  →  raw × 10⁻³ × 1000 = mA
      ∴  raw = A × 1000  (milliampere, mA)
      e.g. 14.49 A → raw = 14 490

  FREQUENCY            → SCALE_FACTOR_MINUS_3  → channel MILLIHERTZ
      raw × 10⁻³ = Hz  →  raw × 10⁻³ × 1000 = mHz
      ∴  raw = Hz × 1000  (millihertz, mHz)
      e.g. 50.000 Hz → raw = 50 000

  ACTIVE / REACTIVE POWER → no scale factor → channel WATT / VAR
      ∴  raw = W (signed 32-bit)

  APPARENT POWER        → no scale factor → channel VOLT_AMPERE
      ∴  raw = VA (unsigned 32-bit)

  POWER FACTOR         → SCALE_FACTOR_MINUS_3  → channel NONE (dimensionless float)
      raw × 10⁻³ = PF  →  raw = PF × 1000  (signed 16-bit, −1000 … +1000)
      e.g. PF 0.952 → raw = 952

  ENERGY (Ea+)         → SCALE_FACTOR_3        → channel CUMULATED_WATT_HOURS
      raw × 10³ = Wh  →  raw = Wh / 1000 = kWh
      ∴  raw = energy in kWh (unsigned 32-bit integer part)

Power factor simulation:
  - Load-dependent sigmoid curve:  0 % load → PF ≈ 0.50
                                   50 % load → PF ≈ 0.87
                                  100 % load → PF ≈ 0.95
  - Ornstein-Uhlenbeck slow drift: ±0.02 on top of the curve
  - Per-phase current imbalance: ±0.5 % fixed seed per load slot
"""

import tkinter as tk
from tkinter import ttk, filedialog
import threading
import time
import random
import math
import csv
import os
import json
from pymodbus.server.sync import StartTcpServer
from pymodbus.device import ModbusDeviceIdentification
from pymodbus.datastore import ModbusSequentialDataBlock, ModbusSlaveContext, ModbusServerContext


# ── Register base addresses ───────────────────────────────────────────────────

LOAD_ADDRESSES = {
    1: 18432,  # 0x4800
    2: 20480,  # 0x5000
    3: 22528,  # 0x5800
    4: 24576,  # 0x6000
    5: 26624,  # 0x6800
    6: 28672,  # 0x7000
}

ENERGY_ADDRESSES = {
    1: 19841,  # 0x4D81
    2: 21889,  # 0x5581
    3: 23937,  # 0x5D81
    4: 25985,  # 0x6581
    5: 28033,  # 0x6D81
    6: 30081,  # 0x7581
}

# ── Meter type definitions ────────────────────────────────────────────────────

METER_TYPES = {
    "I-60": {
        "max_loads": 6,
        "extended_name": "Digiware I-60   ",   # 16 chars
        "product_name":  "DIRIS Digiware  ",
    },
    "I-30": {
        "max_loads": 3,
        "extended_name": "Digiware I-30   ",
        "product_name":  "DIRIS Digiware  ",
    },
    "I-35": {
        "max_loads": 3,
        "extended_name": "Digiware I-35   ",
        "product_name":  "DIRIS Digiware  ",
    },
}

ADDR_SOCO      = 0xC350
ADDR_PROD_NAME = 0xC382
ADDR_EXT_NAME  = 0xC38A

# ── Electrical constants ──────────────────────────────────────────────────────

NOMINAL_VOLTAGE_V = 230.0    # Line-to-Neutral (V)
NOMINAL_FREQ_HZ   = 50.0     # Hz
RATED_POWER_W     = 10_000   # 10 kW rated per load slot


# ── Power factor model (Ornstein-Uhlenbeck + sigmoid curve) ──────────────────

def _compute_power_factor(load_fraction: float, pf_state: dict) -> float:
    """
    Realistic load-dependent power factor.

    Sigmoid curve:
      0 %  load → PF ≈ 0.50  (high magnetising current, inductive)
      25 % load → PF ≈ 0.75
      50 % load → PF ≈ 0.87
      75 % load → PF ≈ 0.93
      100% load → PF ≈ 0.95

    Ornstein–Uhlenbeck mean-reverting noise adds slow ±0.02 drift.
    """
    pf_min, pf_max = 0.50, 0.96
    k, C = 0.6, 0.08
    x = max(load_fraction, 0.0001)
    curve_pf = pf_min + (pf_max - pf_min) * (x ** k) / ((x ** k) + C)

    # OU noise
    theta, sigma = 0.05, 0.003
    noise = pf_state.get("noise", 0.0)
    noise += theta * (0.0 - noise) * 1.0 + sigma * random.gauss(0, 1)
    noise = max(-0.04, min(0.04, noise))
    pf_state["noise"] = noise

    return max(0.40, min(0.999, curve_pf + noise))


# ── Load simulator ────────────────────────────────────────────────────────────

class LoadSimulator:
    """Simulates one load slot within a Digiware meter."""

    def __init__(self, load_number, initial_energy_kwh=0.0):
        self.load_number      = load_number
        self.power_setpoint_w = 0.0
        self.energy_kwh       = initial_energy_kwh
        self.last_update_time = time.time()

        self.voltage_ln_v  = NOMINAL_VOLTAGE_V
        self.frequency_hz  = NOMINAL_FREQ_HZ

        # Fixed per-phase imbalance seeds (±0.5 %)
        rng = random.Random(load_number * 137)
        self._phase_imbalance = [
            1.0 + rng.uniform(-0.005, 0.005),
            1.0 + rng.uniform(-0.005, 0.005),
            1.0 + rng.uniform(-0.005, 0.005),
        ]

        self._pf_state = {"noise": 0.0}

        self.base_addr        = LOAD_ADDRESSES[load_number]
        self.energy_base_addr = ENERGY_ADDRESSES[load_number]

        self.max_power_w      = RATED_POWER_W
        self.max_reactive_var = RATED_POWER_W
        self.power_setpoint_w = 0.0
        self.reactive_setpoint_var = 0.0
        self.simulate_jitter  = False  # Toggle for "simulate data"

        # UI references
        self.control_window = None
        self.control_labels = None
        self.power_label    = None
        self.pf_label       = None
        self.q_label        = None  # Added for reactive power display

    def set_power(self, power_w: float):
        self.power_setpoint_w = float(power_w)

    def set_reactive_power(self, reactive_var: float):
        self.reactive_setpoint_var = float(reactive_var)

    def get_display_values(self) -> dict:
        p_w = self.power_setpoint_w
        q_var = self.reactive_setpoint_var
        s_va = math.sqrt(p_w**2 + q_var**2)
        pf = abs(p_w) / s_va if s_va > 0 else 1.0

        i_a = (s_va / (3 * self.voltage_ln_v) if s_va != 0 else 0.0)

        return {
            "voltage_ln_v": self.voltage_ln_v,
            "current_a":    i_a,
            "power_w":      p_w,
            "reactive_var": q_var,
            "power_factor": pf,
            "frequency_hz": self.frequency_hz,
            "energy_kwh":   self.energy_kwh,
        }

    def update_values(self, datablock):
        """Compute quantities and write to Modbus registers."""

        now  = time.time()
        dt_h = (now - self.last_update_time) / 3600.0
        self.last_update_time = now

        # ── Voltage (with tiny Gaussian noise) ──────────────────────────────
        v_noise = random.gauss(0, 0.0015)
        v_ln_v  = self.voltage_ln_v * (1.0 + v_noise)
        v_ll_v  = v_ln_v * math.sqrt(3)

        # Register encoding: raw = V × 100  (centivolt)
        # Java: raw × SCALE_FACTOR_MINUS_2 → V; channel unit: MILLIVOLT
        # → OpenEMS stores  raw × 10⁻² × 1000 = mV correctly
        v_ln_raw = int(round(v_ln_v * 100))
        v_ll_raw = int(round(v_ll_v * 100))

        # ── Frequency ────────────────────────────────────────────────────────
        f_noise  = random.gauss(0, 0.00005)
        freq_hz  = self.frequency_hz * (1.0 + f_noise)

        # Register encoding: raw = Hz × 1000  (millihertz)
        # Java: raw × SCALE_FACTOR_MINUS_3 → Hz; channel unit: MILLIHERTZ
        # → OpenEMS stores  raw × 10⁻³ × 1000 = mHz correctly
        freq_raw = int(round(freq_hz * 1000))

        # ── Simulation Jitter ("simulate data") ──────────────────────────────
        if self.simulate_jitter:
            # Small random walk for P and Q
            p_drift = random.uniform(-10, 10)
            q_drift = random.uniform(-5, 5)
            self.power_setpoint_w = max(0, min(self.max_power_w, self.power_setpoint_w + p_drift))
            self.reactive_setpoint_var = max(-self.max_reactive_var, min(self.max_reactive_var, self.reactive_setpoint_var + q_drift))

        # ── Power values ─────────────────────────────────────────────────────
        p_w   = self.power_setpoint_w
        q_var = self.reactive_setpoint_var
        s_va  = math.sqrt(p_w**2 + q_var**2)
        pf    = abs(p_w) / s_va if s_va > 0 else 1.0

        # ── Current ──────────────────────────────────────────────────────────
        # I = S / (3 * V_ln)
        if s_va != 0:
            i_avg_a = s_va / (3.0 * v_ln_v)
        else:
            i_avg_a = 0.0

        # Register encoding: raw = A × 1000  (milliampere)
        # Java: raw × SCALE_FACTOR_MINUS_3 → A; channel unit: MILLIAMPERE
        # → OpenEMS stores  raw × 10⁻³ × 1000 = mA correctly
        def phase_raw(imbalance):
            noise = random.gauss(0, 0.008)
            return int(round(i_avg_a * imbalance * (1.0 + noise) * 1000))

        i1_raw = phase_raw(self._phase_imbalance[0])
        i2_raw = phase_raw(self._phase_imbalance[1])
        i3_raw = phase_raw(self._phase_imbalance[2])
        in_raw = abs(i1_raw - i2_raw)   # neutral ≈ residual imbalance

        # ── Final register values ────────────────────────────────────────────
        p_w_raw = int(round(p_w))
        q_var_raw = int(round(q_var))
        s_va_raw = int(round(s_va))
        snom_raw = int(round(self.max_power_w))

        # Power factor register: raw = PF × 1000, signed 16-bit
        # Positive PF in common meters usually means consumption.
        pf_raw = int(round(pf * 1000))

        # ── Energy accumulation ───────────────────────────────────────────────
        if self.power_setpoint_w > 0:
            self.energy_kwh += (self.power_setpoint_w * dt_h) / 1000.0

        # Register encoding: raw = kWh (integer)
        # Java: raw × SCALE_FACTOR_3 → Wh; channel unit: CUMULATED_WATT_HOURS
        # → OpenEMS stores  raw × 1000 = Wh correctly
        energy_int  = int(self.energy_kwh)
        energy_frac = int((self.energy_kwh - energy_int) * 10_000) % 10_000

        # ── Write to datablock ────────────────────────────────────────────────
        db = datablock

        self._write_u16(db, self.base_addr + 0,  1)          # Load status = enabled

        # Offsets 10-11: Frequency (mHz)
        self._write_u32(db, self.base_addr + 10, freq_raw)

        # Offsets 12-17: Phase voltages L-N (cV)
        self._write_u32(db, self.base_addr + 12, v_ln_raw)   # V1
        self._write_u32(db, self.base_addr + 14, v_ln_raw)   # V2
        self._write_u32(db, self.base_addr + 16, v_ln_raw)   # V3

        # Offsets 20-25: Line-to-line voltages (cV)
        self._write_u32(db, self.base_addr + 20, v_ll_raw)   # U12
        self._write_u32(db, self.base_addr + 22, v_ll_raw)   # U23
        self._write_u32(db, self.base_addr + 24, v_ll_raw)   # U31

        # Offsets 26-33: Phase currents (mA) + neutral
        self._write_u32(db, self.base_addr + 26, i1_raw)     # I1
        self._write_u32(db, self.base_addr + 28, i2_raw)     # I2
        self._write_u32(db, self.base_addr + 30, i3_raw)     # I3
        self._write_u32(db, self.base_addr + 32, in_raw)     # In (not mapped in Java)

        # Offsets 42-55: Power block
        self._write_u32(db, self.base_addr + 42, snom_raw)             # Snom
        self._write_s32(db, self.base_addr + 44, p_w_raw)              # P active (W)
        self._write_s32(db, self.base_addr + 46, q_var_raw)            # Q reactive (VAR)
        self._write_s32(db, self.base_addr + 48, max(0,  q_var_raw))   # Q+ lagging
        self._write_s32(db, self.base_addr + 50, max(0, -q_var_raw))   # Q- leading
        self._write_u32(db, self.base_addr + 52, s_va_raw)             # S apparent (VA)
        self._write_s16(db, self.base_addr + 54, pf_raw)               # PF ×1000
        self._write_u16(db, self.base_addr + 55,
                        2 if q_var_raw > 0 else 1 if q_var_raw < 0 else 0)    # Quadrant

        # Energy registers: Ea+ integer kWh + fractional
        self._write_u32(db, self.energy_base_addr + 0, energy_int)
        self._write_u16(db, self.energy_base_addr + 2, energy_frac)
        self._write_u32(db, self.energy_base_addr + 3, 0)   # Ea- = 0 (no production)
        self._write_u16(db, self.energy_base_addr + 5, 0)

    # ── Register helpers ──────────────────────────────────────────────────────

    def _write_u16(self, db, address, value):
        db.setValues(address + 1, [int(value) & 0xFFFF])

    def _write_s16(self, db, address, value):
        v = int(value)
        if v < 0:
            v = (1 << 16) + v
        db.setValues(address + 1, [v & 0xFFFF])

    def _write_u32(self, db, address, value):
        v = int(value) & 0xFFFFFFFF
        db.setValues(address + 1, [(v >> 16) & 0xFFFF, v & 0xFFFF])

    def _write_s32(self, db, address, value):
        v = int(value)
        if v < 0:
            v = (1 << 32) + v
        self._write_u32(db, address, v)


# ── Meter ─────────────────────────────────────────────────────────────────────

class I60Meter:
    """One physical Socomec Digiware meter (I-60 / I-30 / I-35)."""

    def __init__(self, unit_id, meter_type="I-60"):
        self.unit_id    = unit_id
        self.meter_type = meter_type
        self.max_loads  = METER_TYPES[meter_type]["max_loads"]
        self.loads      = {}
        self.datablock  = ModbusSequentialDataBlock(0, [0] * 65536)
        self._write_identification()

    def _write_identification(self):
        db = self.datablock
        db.setValues(ADDR_SOCO + 1, [0x0053, 0x004F, 0x0043, 0x004F])
        db.setValues(ADDR_EXT_NAME  + 1,
                     self._encode_string_norm(METER_TYPES[self.meter_type]["extended_name"], 8))
        db.setValues(ADDR_PROD_NAME + 1,
                     self._encode_string_norm(METER_TYPES[self.meter_type]["product_name"],  8))

    @staticmethod
    def _encode_string_norm(text, num_words):
        padded = text.ljust(num_words * 2, '\x00')
        return [
            (ord(padded[i * 2]) << 8) | ord(padded[i * 2 + 1])
            for i in range(num_words)
        ]

    def add_load(self, load_number, initial_energy=0.0):
        if load_number in self.loads:
            return False, "already_active"
        if load_number > self.max_loads:
            return False, "exceeds_max"
        self.loads[load_number] = LoadSimulator(load_number, initial_energy)
        return True, None

    def remove_load(self, load_number):
        if load_number in self.loads:
            load = self.loads[load_number]
            if load.control_window:
                load.control_window.destroy()
            del self.loads[load_number]
            return True
        return False

    def update_all_loads(self):
        for load in self.loads.values():
            load.update_values(self.datablock)

    def get_load(self, n):
        return self.loads.get(n)

    def get_active_loads(self):
        return sorted(self.loads.keys())


# ── Modbus server ─────────────────────────────────────────────────────────────

class ModbusServerThread(threading.Thread):

    def __init__(self, meters):
        super().__init__(daemon=True)
        self.meters = meters

        slaves = {
            uid: ModbusSlaveContext(
                di=ModbusSequentialDataBlock(0, [0] * 100),
                co=ModbusSequentialDataBlock(0, [0] * 100),
                hr=meter.datablock,
                ir=meter.datablock,
            )
            for uid, meter in meters.items()
        }
        self.context  = ModbusServerContext(slaves=slaves, single=False)
        self.identity = ModbusDeviceIdentification()
        self.identity.VendorName         = "Socomec Simulator"
        self.identity.ProductCode        = "DIGIWARE-I60-SIM"
        self.identity.ProductName        = "Socomec Digiware I60 Simulator"
        self.identity.ModelName          = "I60"
        self.identity.MajorMinorRevision = "4.0.0"

    def run(self):
        print("Starting Modbus TCP server on port 502 …")
        try:
            StartTcpServer(context=self.context, identity=self.identity,
                           address=("0.0.0.0", 502))
        except Exception as e:
            print(f"Modbus server error: {e}")


# ── GUI ───────────────────────────────────────────────────────────────────────

class SimulatorGUI:

    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Socomec Digiware I60 Simulator v4")
        self.root.geometry("1020x740")

        self.meters        = {}
        self.modbus_server = None
        self.state_file    = os.path.join(os.path.dirname(__file__), "last_session.json")
        self.energy_cache  = {}

        self._load_state()
        self._create_widgets()
        
        # Auto-restore active meters from state
        self.root.after(500, self._restore_active_meters)
        
        self.root.protocol("WM_DELETE_WINDOW", self._on_exit)

    def _on_exit(self):
        self._save_state()
        self.root.destroy()

    # ── State Management ──────────────────────────────────────────────────────
    
    def _load_state(self):
        """Loads both historical energy and previous session state from JSON."""
        # 1. Try to migrate from old CSV if JSON doesn't exist yet
        csv_path = os.path.join(os.path.dirname(__file__), "i60_meter_energy_cache_v4.csv")
        if not os.path.exists(self.state_file) and os.path.exists(csv_path):
            try:
                with open(csv_path, newline="") as f:
                    for row in csv.reader(f):
                        if len(row) >= 2:
                            self.energy_cache[row[0]] = float(row[1])
                print(f"Migrated {len(self.energy_cache)} entries from old CSV")
            except: pass

        # 2. Load from JSON state file
        if os.path.exists(self.state_file):
            try:
                with open(self.state_file, "r") as f:
                    data = json.load(f)
                    # Load historical energy registry
                    registry = data.get("energy_registry", {})
                    self.energy_cache.update(registry)
                    # Store data for later restoration
                    self._last_session_data = data.get("active_session", [])
                print(f"Loaded {len(self.energy_cache)} energy records from state file")
            except Exception as e:
                print(f"Error loading state: {e}")

    def _save_state(self):
        """Saves current energy levels and active session config to JSON."""
        try:
            # Update cache with current active meters
            for uid, meter in self.meters.items():
                for ln, load in meter.loads.items():
                    self.energy_cache[f"{uid}_{ln}"] = load.energy_kwh

            # Prepare active session data
            active_session = []
            for uid, meter in self.meters.items():
                m_data = {"unit_id": uid, "meter_type": meter.meter_type, "loads": []}
                for ln, load in meter.loads.items():
                    m_data["loads"].append({
                        "load_number": ln,
                        "max_power_w": load.max_power_w,
                        "max_reactive_var": load.max_reactive_var,
                        "power_setpoint_w": load.power_setpoint_w,
                        "reactive_setpoint_var": load.reactive_setpoint_var,
                        "simulate_jitter": load.simulate_jitter,
                        "energy_kwh": load.energy_kwh
                    })
                active_session.append(m_data)

            # Consolidate into one JSON structure
            full_state = {
                "energy_registry": self.energy_cache,
                "active_session": active_session
            }

            with open(self.state_file, "w") as f:
                json.dump(full_state, f, indent=2)
        except Exception as e:
            pass

    def _restore_active_meters(self):
        """Re-instantiates meters that were active in the last session."""
        if not hasattr(self, "_last_session_data") or not self._last_session_data:
            return
            
        try:
            count = 0
            for m_data in self._last_session_data:
                uid = m_data["unit_id"]
                m_type = m_data["meter_type"]
                
                if uid not in self.meters:
                    self.meters[uid] = I60Meter(uid, m_type)
                
                for l_data in m_data["loads"]:
                    ln = l_data["load_number"]
                    # Use registry energy (most up to date)
                    energy = self.energy_cache.get(f"{uid}_{ln}", l_data.get("energy_kwh", 0.0))
                        
                    self.meters[uid].add_load(ln, energy)
                    load = self.meters[uid].get_load(ln)
                    load.max_power_w = l_data.get("max_power_w", 10000)
                    load.max_reactive_var = l_data.get("max_reactive_var", 10000)
                    load.power_setpoint_w = l_data.get("power_setpoint_w", 0.0)
                    load.reactive_setpoint_var = l_data.get("reactive_setpoint_var", 0.0)
                    load.simulate_jitter = l_data.get("simulate_jitter", False)
                    count += 1
            
            if count > 0:
                self._refresh_meters_display()
                self._restart_server()
                print(f"Auto-restored {count} load(s).")
        except Exception as e:
            print(f"Restore session error: {e}")

    # ── Profiles ──────────────────────────────────────────────────────────────

    def _save_profile(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON profiles", "*.json"), ("All files", "*.*")],
            title="Save Meter Profile"
        )
        if not path: return

        data = {"meters": []}
        for uid, meter in self.meters.items():
            m_data = {"unit_id": uid, "meter_type": meter.meter_type, "loads": []}
            for ln, load in meter.loads.items():
                m_data["loads"].append({
                    "load_number": ln,
                    "max_power_w": load.max_power_w,
                    "max_reactive_var": load.max_reactive_var,
                    "power_setpoint_w": load.power_setpoint_w,
                    "reactive_setpoint_var": load.reactive_setpoint_var,
                    "simulate_jitter": load.simulate_jitter,
                    "energy_kwh": load.energy_kwh
                })
            data["meters"].append(m_data)

        with open(path, "w") as f:
            json.dump(data, f, indent=2)
        print(f"Profile saved: {path}")

    def _load_profile(self):
        path = filedialog.askopenfilename(
            filetypes=[("JSON profiles", "*.json"), ("All files", "*.*")],
            title="Load Meter Profile"
        )
        if not path: return

        with open(path, "r") as f:
            data = json.load(f)

        # Clear current setup
        for uid in list(self.meters.keys()):
            for ln in list(self.meters[uid].loads.keys()):
                self.meters[uid].remove_load(ln)
            del self.meters[uid]

        # Reconstruct
        for m_data in data["meters"]:
            uid = m_data["unit_id"]
            m_type = m_data["meter_type"]
            self.meters[uid] = I60Meter(uid, m_type)
            for l_data in m_data["loads"]:
                ln = l_data["load_number"]
                self.meters[uid].add_load(ln, l_data.get("energy_kwh", 0.0))
                load = self.meters[uid].get_load(ln)
                load.max_power_w = l_data.get("max_power_w", 10000)
                load.max_reactive_var = l_data.get("max_reactive_var", 10000)
                load.power_setpoint_w = l_data.get("power_setpoint_w", 0.0)
                load.reactive_setpoint_var = l_data.get("reactive_setpoint_var", 0.0)
                load.simulate_jitter = l_data.get("simulate_jitter", False)

        self._refresh_meters_display()
        self._restart_server()
        print(f"Profile loaded: {path}")

    # ── Widget construction ───────────────────────────────────────────────────

    def _create_widgets(self):
        tk.Label(self.root,
                 text="Socomec Digiware I60 Multi-Load Simulator v4",
                 font=("Arial", 16, "bold"), fg="#1A237E").pack(pady=10)

        # ── Profile Management ────────────────────────────────────────────────
        prof_frame = tk.LabelFrame(self.root, text="Profile Management", font=("Arial", 10, "bold"), padx=10, pady=5)
        prof_frame.pack(fill=tk.X, padx=20, pady=5)

        tk.Button(prof_frame, text="📁 Load Profile from File…", command=self._load_profile,
                  bg="#FF9800", fg="white", font=("Arial", 9, "bold"), padx=10).pack(side=tk.LEFT, padx=5)

        tk.Button(prof_frame, text="💾 Save Current Setup As…", command=self._save_profile,
                  bg="#3F51B5", fg="white", font=("Arial", 9, "bold"), padx=10).pack(side=tk.LEFT, padx=5)

        ctrl = tk.Frame(self.root)
        ctrl.pack(pady=8, fill=tk.X, padx=20)

        tk.Label(ctrl, text="Activate Load:", font=("Arial", 11, "bold")).pack(side=tk.LEFT, padx=5)

        tk.Label(ctrl, text="Unit ID:", font=("Arial", 10)).pack(side=tk.LEFT, padx=(10, 5))
        self.unit_id_var = tk.IntVar(value=1)
        tk.Spinbox(ctrl, from_=1, to=247, textvariable=self.unit_id_var,
                   width=5, font=("Arial", 10)).pack(side=tk.LEFT, padx=5)

        tk.Label(ctrl, text="Meter Type:", font=("Arial", 10)).pack(side=tk.LEFT, padx=(10, 5))
        self.meter_type_var = tk.StringVar(value="I-60")
        mt_dd = ttk.Combobox(ctrl, textvariable=self.meter_type_var,
                              values=list(METER_TYPES.keys()),
                              state="readonly", width=6, font=("Arial", 10))
        mt_dd.pack(side=tk.LEFT, padx=5)

        tk.Label(ctrl, text="Load:", font=("Arial", 10)).pack(side=tk.LEFT, padx=(10, 5))
        self.load_var = tk.IntVar(value=1)
        self.load_dropdown = ttk.Combobox(ctrl, textvariable=self.load_var,
                                          values=[1,2,3,4,5,6],
                                          state="readonly", width=5, font=("Arial", 10))
        self.load_dropdown.pack(side=tk.LEFT, padx=5)

        def _on_type_change(*_):
            ml = METER_TYPES[self.meter_type_var.get()]["max_loads"]
            self.load_dropdown["values"] = list(range(1, ml + 1))
            if self.load_var.get() > ml:
                self.load_var.set(1)
        self.meter_type_var.trace_add("write", _on_type_change)

        tk.Button(ctrl, text="+ Activate Load", command=self._add_load,
                  bg="#4CAF50", fg="white", font=("Arial", 10, "bold"),
                  padx=15, pady=5).pack(side=tk.LEFT, padx=10)

        self.server_status = tk.Label(ctrl, text="Server: Not Started",
                                      font=("Arial", 9), fg="red")
        self.server_status.pack(side=tk.RIGHT, padx=10)

        lf = tk.LabelFrame(self.root, text="Active Meters and Loads",
                           font=("Arial", 12, "bold"), padx=10, pady=10)
        lf.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)

        canvas = tk.Canvas(lf)
        sb = tk.Scrollbar(lf, orient="vertical", command=canvas.yview)
        self.meters_frame = tk.Frame(canvas)
        self.meters_frame.bind("<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=self.meters_frame, anchor="nw")
        canvas.configure(yscrollcommand=sb.set)
        canvas.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        self.instructions = tk.Label(self.root,
            text="Select Unit ID and Load, then click '+ Activate Load'",
            font=("Arial", 9), fg="gray")
        self.instructions.pack(pady=5)

    # ── Load management ───────────────────────────────────────────────────────

    def _add_load(self):
        uid        = self.unit_id_var.get()
        load_num   = self.load_var.get()
        meter_type = self.meter_type_var.get()

        if uid in self.meters:
            if self.meters[uid].meter_type != meter_type:
                self._error("Unit ID Conflict",
                            f"Unit ID {uid} is already a {self.meters[uid].meter_type} meter.")
                return
        else:
            self.meters[uid] = I60Meter(uid, meter_type)
            print(f"Created {meter_type} meter — Unit ID {uid}")

        meter = self.meters[uid]
        key   = f"{uid}_{load_num}"
        init  = self.energy_cache.get(key, 0.0)

        ok, reason = meter.add_load(load_num, init)
        if not ok:
            msg = (f"Load {load_num} on Unit ID {uid} is already active!"
                   if reason == "already_active"
                   else f"{meter.meter_type} supports loads 1–{meter.max_loads} only.")
            self._error("Load Error", msg)
            return

        meter.update_all_loads()
        self._refresh_meters_display()
        self._restart_server()
        print(f"Activated Load {load_num} on Unit ID {uid} ({meter.meter_type})")

    def _remove_load(self, uid, load_num):
        if uid in self.meters:
            self.meters[uid].remove_load(load_num)
            if not self.meters[uid].loads:
                del self.meters[uid]
            self._refresh_meters_display()
            self._restart_server()

    def _error(self, title, message):
        w = tk.Toplevel(self.root)
        w.title(title)
        w.geometry("440x160")
        tk.Label(w, text=f"⚠️  {title}",
                 font=("Arial", 13, "bold"), fg="red").pack(pady=14)
        tk.Label(w, text=message, font=("Arial", 10), justify="center").pack(pady=5)
        tk.Button(w, text="OK", command=w.destroy,
                  bg="#2196F3", fg="white", font=("Arial", 10),
                  padx=20, pady=5).pack(pady=10)

    # ── Display ───────────────────────────────────────────────────────────────

    def _refresh_meters_display(self):
        for w in self.meters_frame.winfo_children():
            w.destroy()

        if not self.meters:
            tk.Label(self.meters_frame,
                     text="No meters active. Add a load to get started.",
                     font=("Arial", 10), fg="gray").pack(pady=20)
            return

        for uid in sorted(self.meters.keys()):
            meter = self.meters[uid]
            mf = tk.LabelFrame(self.meters_frame,
                               text=f"Unit ID {uid} — {meter.meter_type}  (max {meter.max_loads} loads)",
                               font=("Arial", 11, "bold"), padx=10, pady=5, bg="#f0f0f0")
            mf.pack(fill=tk.X, pady=5, padx=5)

            for ln in meter.get_active_loads():
                load = meter.get_load(ln)
                row  = tk.Frame(mf, bg="#ffffff", relief=tk.RIDGE, bd=1, padx=8, pady=5)
                row.pack(fill=tk.X, pady=2)

                tk.Label(row, text=f"Load {ln}", font=("Arial", 10, "bold"),
                         width=8, anchor="w", bg="#ffffff").pack(side=tk.LEFT, padx=5)

                pl = tk.Label(row, text="P: 0 W", font=("Arial", 9),
                               width=12, anchor="w", bg="#ffffff")
                pl.pack(side=tk.LEFT, padx=5)
                load.power_label = pl

                ql = tk.Label(row, text="Q: 0 VAR", font=("Arial", 9),
                               width=12, anchor="w", bg="#ffffff")
                ql.pack(side=tk.LEFT, padx=5)
                load.q_label = ql

                pfl = tk.Label(row, text="PF: —", font=("Arial", 9),
                                width=10, anchor="w", bg="#ffffff", fg="#555")
                pfl.pack(side=tk.LEFT, padx=5)
                load.pf_label = pfl

                tk.Button(row, text="Open Controls",
                          command=lambda u=uid, l=ln: self._open_load_window(u, l),
                          bg="#607D8B", fg="white", font=("Arial", 9),
                          padx=10, pady=3).pack(side=tk.LEFT, padx=5)

                tk.Button(row, text="Deactivate",
                          command=lambda u=uid, l=ln: self._remove_load(u, l),
                          bg="#f44336", fg="white", font=("Arial", 9),
                          padx=10, pady=3).pack(side=tk.LEFT, padx=5)

    # ── Control window ────────────────────────────────────────────────────────

    def _open_load_window(self, uid, load_num):
        meter = self.meters.get(uid)
        if not meter:
            return
        load = meter.get_load(load_num)
        if not load:
            return

        if load.control_window and load.control_window.winfo_exists():
            load.control_window.lift()
            return

        win = tk.Toplevel(self.root)
        win.title(f"Unit ID {uid} ({meter.meter_type}) — Load {load_num}")
        win.geometry("620x680")

        tk.Label(win, text=f"Unit ID {uid}  ·  {meter.meter_type}",
                 font=("Arial", 14, "bold")).pack(pady=10)
        tk.Label(win, text=f"Load {load_num}", font=("Arial", 12), fg="blue").pack()
        tk.Label(win,
                 text=f"Inst base: 0x{load.base_addr:04X}  |  Energy base: 0x{load.energy_base_addr:04X}",
                 font=("Arial", 8), fg="gray").pack()

        # ── Scaling legend ────────────────────────────────────────────────────
        scale_frame = tk.LabelFrame(win, text="Register encoding  (matches Java SCALE_FACTOR)",
                                    font=("Arial", 8, "bold"), padx=8, pady=4)
        scale_frame.pack(fill=tk.X, padx=18, pady=(6, 0))
        scales = [
            ("Voltage",   "raw = V × 100  (cV)",        "× 10⁻²  → V,  ch: mV"),
            ("Current",   "raw = A × 1000 (mA)",        "× 10⁻³  → A,  ch: mA"),
            ("Frequency", "raw = Hz × 1000 (mHz)",      "× 10⁻³  → Hz, ch: mHz"),
            ("Power",     "raw = W  (signed 32-bit)",   "no scale,      ch: W"),
            ("PF",        "raw = PF × 1000",            "× 10⁻³  → PF, ch: —"),
            ("Energy",    "raw = kWh (uint 32-bit)",    "× 10³   → Wh, ch: Wh"),
        ]
        for i, (qty, enc, java) in enumerate(scales):
            col = (i % 2) * 3
            row = i // 2
            tk.Label(scale_frame, text=f"{qty}:", font=("Arial", 7, "bold"),
                     anchor="e", width=8).grid(row=row, column=col,   sticky="e")
            tk.Label(scale_frame, text=enc,       font=("Arial", 7),
                     anchor="w", width=22).grid(row=row, column=col+1, sticky="w")
            tk.Label(scale_frame, text=java,      font=("Arial", 7), fg="#888",
                     anchor="w", width=24).grid(row=row, column=col+2, sticky="w")

        # ── Active Power slider ───────────────────────────────────────────────
        p_frame = tk.Frame(win)
        p_frame.pack(fill=tk.X, padx=20, pady=(12, 0))

        tk.Label(p_frame, text="Active Power — Consumption (W)",
                 font=("Arial", 11, "bold")).pack(side=tk.TOP, anchor="w")

        p_ctrl_frame = tk.Frame(p_frame)
        p_ctrl_frame.pack(fill=tk.X, pady=5)

        pwr_lbl = tk.Label(p_ctrl_frame, text=f"{load.power_setpoint_w:.0f} W", font=("Arial", 12, "bold"), width=10)
        pwr_lbl.pack(side=tk.LEFT)

        sl_p = tk.Scale(p_ctrl_frame, from_=0, to=load.max_power_w, orient=tk.HORIZONTAL, length=300,
                        command=lambda v: self._on_power_change(uid, load_num, pwr_lbl, v))
        sl_p.set(int(load.power_setpoint_w))
        sl_p.pack(side=tk.LEFT, padx=10)

        tk.Label(p_ctrl_frame, text="Max:", font=("Arial", 9)).pack(side=tk.LEFT)
        max_p_var = tk.StringVar(value=str(int(load.max_power_w)))
        max_p_ent = tk.Entry(p_ctrl_frame, textvariable=max_p_var, width=8)
        max_p_ent.pack(side=tk.LEFT, padx=5)
        max_p_ent.bind("<Return>", lambda e: self._on_max_power_change(uid, load_num, sl_p, max_p_var.get()))
        max_p_ent.bind("<FocusOut>", lambda e: self._on_max_power_change(uid, load_num, sl_p, max_p_var.get()))

        # ── Reactive Power slider ─────────────────────────────────────────────
        q_frame = tk.Frame(win)
        q_frame.pack(fill=tk.X, padx=20, pady=(12, 0))

        tk.Label(q_frame, text="Reactive Power (VAR)  [+ Inductive, - Capacitive]",
                 font=("Arial", 11, "bold")).pack(side=tk.TOP, anchor="w")

        q_ctrl_frame = tk.Frame(q_frame)
        q_ctrl_frame.pack(fill=tk.X, pady=5)

        q_lbl = tk.Label(q_ctrl_frame, text=f"{load.reactive_setpoint_var:.0f} VAR", font=("Arial", 12, "bold"), width=10)
        q_lbl.pack(side=tk.LEFT)

        sl_q = tk.Scale(q_ctrl_frame, from_=-load.max_reactive_var, to=load.max_reactive_var, orient=tk.HORIZONTAL, length=300,
                        command=lambda v: self._on_reactive_change(uid, load_num, q_lbl, v))
        sl_q.set(int(load.reactive_setpoint_var))
        sl_q.pack(side=tk.LEFT, padx=10)

        tk.Label(q_ctrl_frame, text="Max:", font=("Arial", 9)).pack(side=tk.LEFT)
        max_q_var = tk.StringVar(value=str(int(load.max_reactive_var)))
        max_q_ent = tk.Entry(q_ctrl_frame, textvariable=max_q_var, width=8)
        max_q_ent.pack(side=tk.LEFT, padx=5)
        max_q_ent.bind("<Return>", lambda e: self._on_max_reactive_change(uid, load_num, sl_q, max_q_var.get()))
        max_q_ent.bind("<FocusOut>", lambda e: self._on_max_reactive_change(uid, load_num, sl_q, max_q_var.get()))

        # ── Simulation toggle ─────────────────────────────────────────────────
        sim_frame = tk.Frame(win)
        sim_frame.pack(fill=tk.X, padx=20, pady=10)
        sim_var = tk.BooleanVar(value=load.simulate_jitter)
        tk.Checkbutton(sim_frame, text="Enable Real-time Simulation (Data Jitter)",
                       variable=sim_var, font=("Arial", 10, "italic"),
                       command=lambda: setattr(load, "simulate_jitter", sim_var.get())).pack(side=tk.LEFT)

        # ── Live readout ───────────────────────────────────────────────────────
        df = tk.Frame(win)
        df.pack(pady=14)

        def lrow(label, row_idx):
            tk.Label(df, text=label, font=("Arial", 9), anchor="e", width=24).grid(
                row=row_idx, column=0, sticky="e", pady=3)
            lbl = tk.Label(df, text="—", font=("Courier", 9, "bold"), anchor="w", width=46)
            lbl.grid(row=row_idx, column=1, sticky="w", padx=6)
            return lbl

        v_lbl  = lrow("Voltage L-N:",         0)
        i_lbl  = lrow("Current (avg/phase):", 1)
        f_lbl  = lrow("Frequency:",           2)
        pf_lbl = lrow("Power Factor:",        3)
        e_lbl  = lrow("Energy Ea+ (kWh):",    4)

        tk.Label(win,
                 text="PF curve:  0 % load → ~0.50  |  50 % → ~0.87  |  100 % → ~0.95",
                 font=("Arial", 8, "italic"), fg="#777").pack()

        load.control_labels = {
            "power":      pwr_lbl,
            "reactive":   q_lbl,
            "voltage_ln": v_lbl,
            "current":    i_lbl,
            "frequency":  f_lbl,
            "pf":         pf_lbl,
            "energy":     e_lbl,
        }

        def on_close():
            load.control_window = None
            load.control_labels = None
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", on_close)
        load.control_window = win

    def _on_power_change(self, uid, load_num, label, value):
        meter = self.meters.get(uid)
        if not meter: return
        load = meter.get_load(load_num)
        if not load: return
        p = float(value)
        # Only set if not currently jittering or user specifically moved it
        load.set_power(p)
        label.config(text=f"{p:.0f} W", fg="blue" if p != 0 else "gray")
        if load.power_label:
            load.power_label.config(text=f"P: {p:.0f} W")

    def _on_reactive_change(self, uid, load_num, label, value):
        meter = self.meters.get(uid)
        if not meter: return
        load = meter.get_load(load_num)
        if not load: return
        q = float(value)
        load.set_reactive_power(q)
        label.config(text=f"{q:.0f} VAR", fg="purple" if q != 0 else "gray")
        if load.q_label:
            load.q_label.config(text=f"Q: {q:.0f} VAR")

    def _on_max_power_change(self, uid, load_num, slider, value):
        try:
            m = float(value)
            load = self.meters[uid].get_load(load_num)
            load.max_power_w = m
            slider.config(to=m)
        except: pass

    def _on_max_reactive_change(self, uid, load_num, slider, value):
        try:
            m = float(value)
            load = self.meters[uid].get_load(load_num)
            load.max_reactive_var = m
            slider.config(from_=-m, to=m)
        except: pass

    # ── Server ────────────────────────────────────────────────────────────────

    def _restart_server(self):
        if not self.meters:
            self.server_status.config(text="Server: No meters", fg="gray")
            return

        if self.modbus_server is None or not self.modbus_server.is_alive():
            self.modbus_server = ModbusServerThread(self.meters)
            self.modbus_server.start()
            print(f"Modbus server started — {len(self.meters)} meter(s)")
        else:
            for uid, m in self.meters.items():
                self.modbus_server.context[uid] = ModbusSlaveContext(
                    di=ModbusSequentialDataBlock(0, [0] * 100),
                    co=ModbusSequentialDataBlock(0, [0] * 100),
                    hr=m.datablock,
                    ir=m.datablock,
                )

        total = sum(len(m.loads) for m in self.meters.values())
        self.server_status.config(text="Server: Running (Port 502)", fg="green")
        self.instructions.config(
            text=f"Modbus TCP: localhost:502  |  {len(self.meters)} meter(s), {total} load(s) active"
        )

    # ── Periodic update ───────────────────────────────────────────────────────

    def _update_display(self):
        for meter in self.meters.values():
            meter.update_all_loads()

            for load in meter.loads.values():
                vals = load.get_display_values()
                pf   = vals["power_factor"]
                p_w  = vals["power_w"]
                q_v  = vals["reactive_var"]

                if load.power_label:
                    load.power_label.config(text=f"P: {p_w:.0f} W")
                if load.q_label:
                    load.q_label.config(text=f"Q: {q_v:.0f} VAR")
                if load.pf_label:
                    load.pf_label.config(text=f"PF: {pf:.3f}")

                if load.control_labels:
                    cl = load.control_labels
                    v  = vals["voltage_ln_v"]
                    i  = vals["current_a"]
                    f  = vals["frequency_hz"]

                    # Update sliders if simulating
                    if load.simulate_jitter and load.control_window:
                        # Find the scale widgets (heuristic)
                        for child in load.control_window.winfo_children():
                            if isinstance(child, tk.Frame):
                                for grand in child.winfo_children():
                                    if isinstance(grand, tk.Scale):
                                        if "Active" in child.winfo_children()[0].cget("text"):
                                            grand.set(p_w)
                                        elif "Reactive" in child.winfo_children()[0].cget("text"):
                                            grand.set(q_v)

                    # Show actual value + the raw register that Java will read
                    cl["voltage_ln"].config(
                        text=f"{v:.3f} V   → reg {int(round(v*100)):>7}  (cV,  ×10⁻² → {v:.3f} V  → {v*1000:.0f} mV ch)")
                    cl["current"].config(
                        text=f"{i:.4f} A   → reg {int(round(i*1000)):>7}  (mA,  ×10⁻³ → {i:.4f} A → {i*1000:.1f} mA ch)")
                    cl["frequency"].config(
                        text=f"{f:.4f} Hz  → reg {int(round(f*1000)):>7}  (mHz, ×10⁻³ → {f:.4f} Hz → {f*1000:.1f} mHz ch)")
                    cl["pf"].config(
                        text=f"{pf:.4f}      → reg {int(round(pf*1000)):>7}  (×10⁻³ → {pf:.4f})")
                    cl["energy"].config(
                        text=f"{vals['energy_kwh']:.4f} kWh → reg {int(vals['energy_kwh']):>7}  (×10³  → {vals['energy_kwh']*1000:.0f} Wh ch)")

        self._save_state()
        self.root.after(1000, self._update_display)

    def run(self):
        self._update_display()
        self.root.mainloop()


# ── Entry point ───────────────────────────────────────────────────────────────

if __name__ == "__main__":
    print("=" * 72)
    print("Socomec Digiware Multi-Load Meter Simulator v4")
    print()
    print("Register encoding  (matches applyLoadProtocol() scale factors):")
    print()
    print("  Quantity    Raw register value      Java scale      OpenEMS channel")
    print("  ─────────── ──────────────────────  ──────────────  ───────────────")
    print("  Voltage     V × 100  (centivolt)    SCALE_MINUS_2   MILLIVOLT")
    print("  Current     A × 1000 (milliampere)  SCALE_MINUS_3   MILLIAMPERE")
    print("  Frequency   Hz × 1000 (millihertz)  SCALE_MINUS_3   MILLIHERTZ")
    print("  Active P    W  (signed 32-bit)       none            WATT")
    print("  Reactive P  VAR (signed 32-bit)      none            VOLT_AMPERE_REACTIVE")
    print("  Apparent S  VA  (unsigned 32-bit)    none            VOLT_AMPERE")
    print("  Power Fac.  PF × 1000 (signed 16b)  SCALE_MINUS_3   (dimensionless)")
    print("  Energy Ea+  kWh (uint 32-bit)        SCALE_PLUS_3    CUMULATED_WATT_HOURS")
    print()
    print("Power factor model:  sigmoid curve (0 %→0.50, 50 %→0.87, 100 %→0.95)")
    print("                     + Ornstein–Uhlenbeck drift  + per-phase imbalance")
    print("=" * 72)
    print()

    app = SimulatorGUI()
    app.run()