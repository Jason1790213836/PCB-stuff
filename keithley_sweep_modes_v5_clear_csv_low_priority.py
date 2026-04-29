import tkinter as tk
from tkinter import ttk, messagebox
import threading
import time
import csv
import os
import re
import queue
from datetime import datetime

import pyvisa
import matplotlib.pyplot as plt
from matplotlib.figure import Figure
from matplotlib.backends.backend_agg import FigureCanvasAgg
from pyvisa.constants import StopBits, Parity

# =========================
# User configuration
# =========================
USB_RESOURCE_DEFAULT = "USB0::0x05E6::0x2636::MYFP001038::INSTR"
ETH_RESOURCE_DEFAULT = "TCPIP0::169.254.25.205::inst0::INSTR"
COM_RESOURCE_DEFAULT = "ASRL5::INSTR"   # COM5

SAVE_DIR = os.path.join(os.path.expanduser("~"), "Desktop", "keithley")
os.makedirs(SAVE_DIR, exist_ok=True)

K2400_CURRENT_RANGE_DEFAULT = 1e-3
K2400_MIN_CURRENT_FOR_RESISTANCE = 1e-12

CHANNEL_DEVICE_MAP = {
    "A": ("usb", "smua"),
    "B": ("usb", "smub"),
    "C": ("eth", "smua"),
    "D": ("eth", "smub"),
    "E": ("com", "2400"),
}
CHANNEL_ORDER = ["A", "B", "C", "D", "E"]

DEVICE_CHANNELS = {
    "usb": ["A", "B"],
    "eth": ["C", "D"],
    "com": ["E"],
}

UI_POLL_MS = 50
PLOT_REFRESH_EVERY = 5
LOG_REFRESH_EVERY = 10

# =========================
# Global state
# =========================
rm = None
devices = {
    "usb": {"inst": None, "connected": False, "label": "USB Instrument (A/B)"},
    "eth": {"inst": None, "connected": False, "label": "Ethernet Instrument (C/D)"},
    "com": {"inst": None, "connected": False, "label": "Keithley 2400 (E)"},
}

stop_requested = False
producer_threads = {}
producer_done = {"usb": False, "eth": False, "com": False}

paused = {ch: False for ch in CHANNEL_ORDER}
pause_started = {ch: None for ch in CHANNEL_ORDER}
paused_accum = {ch: 0.0 for ch in CHANNEL_ORDER}

plot_data = {
    "A_v": [], "A_i": [],
    "B_v": [], "B_i": [],
    "C_v": [], "C_i": [],
    "D_v": [], "D_i": [],
    "E_v": [], "E_i": [],
}

plot_initialized = False
plot_window_opened = False
channel_vars = {}

# 3 separate buffers
usb_queue = queue.Queue()
eth_queue = queue.Queue()
com_queue = queue.Queue()
QUEUE_MAP = {"usb": usb_queue, "eth": eth_queue, "com": com_queue}

rows_buffer = []
current_run_paths = {"csv": None, "png": None}
consumer_tick_count = 0
run_start_time = None
save_output_started = False
save_status_queue = queue.Queue()

# =========================
# Basic helpers
# =========================
def sanitize_filename(name: str) -> str:
    name = name.strip()
    name = re.sub(r'[<>:"/\\\\|?*]+', "_", name)
    name = re.sub(r"\s+", "_", name)
    name = name.strip("._")
    return name

def make_unique_base_path(base_name: str) -> str:
    base_path = os.path.join(SAVE_DIR, base_name)
    if (not os.path.exists(base_path + ".csv")) and (not os.path.exists(base_path + ".png")):
        return base_path
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    return os.path.join(SAVE_DIR, f"{base_name}_{stamp}")

def log(msg: str):
    log_text.insert(tk.END, msg + "\n")
    log_text.see(tk.END)

def get_inst_for_channel(channel: str):
    device_key, _ = CHANNEL_DEVICE_MAP[channel]
    return devices[device_key]["inst"]

def is_channel_connected(channel: str) -> bool:
    device_key, _ = CHANNEL_DEVICE_MAP[channel]
    return devices[device_key]["connected"]

def is_2400_channel(channel: str) -> bool:
    device_key, _ = CHANNEL_DEVICE_MAP[channel]
    return device_key == "com"

def clear_plot_data():
    for key in plot_data:
        plot_data[key].clear()

# =========================
# 2636B TSP helpers
# =========================
def tsp_write(inst, cmd: str):
    inst.write(cmd)

def tsp_query(inst, cmd: str) -> str:
    return inst.query(cmd).strip()

def tsp_query_float(inst, expr: str) -> float:
    return float(tsp_query(inst, f"print({expr})"))

# =========================
# 2400 SCPI helpers
# =========================
def scpi_write(inst, cmd: str):
    inst.write(cmd)

def scpi_query(inst, cmd: str) -> str:
    return inst.query(cmd).strip()

def init_2400(inst, current_limit: float):
    scpi_write(inst, "*RST")
    scpi_write(inst, "*CLS")
    scpi_write(inst, ":ROUT:TERM REAR")
    scpi_write(inst, ":SOUR:FUNC VOLT")
    scpi_write(inst, ":SENS:FUNC 'CURR'")
    scpi_write(inst, f":SENS:CURR:RANG {K2400_CURRENT_RANGE_DEFAULT}")
    scpi_write(inst, f":SENS:CURR:PROT {current_limit}")
    scpi_write(inst, ":OUTP OFF")

def set_2400_output(inst, on: bool):
    scpi_write(inst, f":OUTP {'ON' if on else 'OFF'}")

def configure_2400_voltage_mode(inst, voltage: float, current_limit: float):
    scpi_write(inst, ":ROUT:TERM REAR")
    scpi_write(inst, ":SOUR:FUNC VOLT")
    scpi_write(inst, ":SENS:FUNC 'CURR'")
    scpi_write(inst, f":SENS:CURR:RANG {K2400_CURRENT_RANGE_DEFAULT}")
    scpi_write(inst, f":SENS:CURR:PROT {current_limit}")
    scpi_write(inst, f":SOUR:VOLT {voltage}")

def measure_2400(inst):
    scpi_write(inst, ":ROUT:TERM REAR")
    reading = scpi_query(inst, ":READ?")
    parts = [p.strip() for p in reading.split(",")]
    if len(parts) < 2:
        raise ValueError(f"Unexpected 2400 reply: {reading}")
    measured_v = float(parts[0])
    measured_i = float(parts[1])
    if abs(measured_v) > 1e37 or abs(measured_i) > 1e37:
        raise ValueError(f"2400 invalid/overflow reading: {reading}")
    return measured_v, measured_i

# =========================
# Plot helpers
# =========================
def init_plot_window():
    global plot_initialized, plot_window_opened
    if plot_window_opened:
        return
    plt.ion()
    plt.figure("Keithley Real-Time Plot", figsize=(10, 6))
    plot_initialized = True
    plot_window_opened = True

def refresh_plot_main_thread():
    if not plot_initialized:
        return

    plt.figure("Keithley Real-Time Plot")
    plt.clf()

    any_data = False
    styles = {
        "A": ("o", "-", "Channel A"),
        "B": ("x", "--", "Channel B"),
        "C": ("s", "-.", "Channel C"),
        "D": ("^", ":", "Channel D"),
        "E": ("d", "-", "Channel E / 2400"),
    }

    for ch in CHANNEL_ORDER:
        if plot_data[f"{ch}_v"]:
            marker, linestyle, label = styles[ch]
            plt.plot(plot_data[f"{ch}_v"], plot_data[f"{ch}_i"],
                     marker=marker, linestyle=linestyle, label=label)
            any_data = True

    plt.xlabel("Voltage (V)")
    plt.ylabel("Current (A)")
    plt.title("Real-Time I-V Plot")
    plt.grid(True)
    if any_data:
        plt.legend()
    plt.tight_layout()
    plt.draw()
    plt.pause(0.001)

def save_plot_file(png_path: str):
    fig = Figure(figsize=(10, 6))
    FigureCanvasAgg(fig)
    ax = fig.add_subplot(111)

    any_data = False
    styles = {
        "A": ("o", "-", "Channel A"),
        "B": ("x", "--", "Channel B"),
        "C": ("s", "-.", "Channel C"),
        "D": ("^", ":", "Channel D"),
        "E": ("d", "-", "Channel E / 2400"),
    }

    for ch in CHANNEL_ORDER:
        if plot_data[f"{ch}_v"]:
            marker, linestyle, label = styles[ch]
            ax.plot(plot_data[f"{ch}_v"], plot_data[f"{ch}_i"],
                    marker=marker, linestyle=linestyle, label=label)
            any_data = True

    ax.set_xlabel("Voltage (V)")
    ax.set_ylabel("Current (A)")
    ax.set_title("Keithley Real-Time I-V Plot")
    ax.grid(True)
    if any_data:
        ax.legend()
    fig.tight_layout()
    fig.savefig(png_path, dpi=150)

# =========================
# Instrument connection
# =========================
def connect_device(device_key: str):
    global rm

    if devices[device_key]["connected"]:
        return

    if device_key == "usb":
        resource = usb_resource_var.get().strip()
    elif device_key == "eth":
        resource = eth_resource_var.get().strip()
    else:
        resource = com_resource_var.get().strip()

    if not resource:
        messagebox.showerror("Error", f"Please enter the VISA resource for {devices[device_key]['label']}.")
        return

    try:
        if rm is None:
            rm = pyvisa.ResourceManager()

        inst = rm.open_resource(resource)

        if device_key in ("usb", "eth"):
            inst.timeout = 10000
            inst.write_termination = "\n"
            inst.read_termination = "\n"

            idn = tsp_query(inst, "*IDN?")
            log(f"{devices[device_key]['label']} connected: {idn}")

            tsp_write(inst, "reset()")
            for ch in ("smua", "smub"):
                tsp_write(inst, f"{ch}.source.func = {ch}.OUTPUT_DCVOLTS")
                tsp_write(inst, f"{ch}.source.levelv = 0")
                tsp_write(inst, f"{ch}.measure.autorangei = {ch}.AUTORANGE_ON")
                tsp_write(inst, f"{ch}.measure.autorangev = {ch}.AUTORANGE_ON")
                tsp_write(inst, f"{ch}.source.output = {ch}.OUTPUT_OFF")
        else:
            inst.baud_rate = 9600
            inst.data_bits = 8
            inst.stop_bits = StopBits.one
            inst.parity = Parity.none
            inst.timeout = 5000
            inst.write_termination = "\r"
            inst.read_termination = "\r"

            idn = scpi_query(inst, "*IDN?")
            log(f"{devices[device_key]['label']} connected: {idn}")

            current_limit = float(channel_vars["E"]["current_limit"].get())
            init_2400(inst, current_limit)

        devices[device_key]["inst"] = inst
        devices[device_key]["connected"] = True

        if device_key == "usb":
            usb_status_var.set("Connected")
        elif device_key == "eth":
            eth_status_var.set("Connected")
        else:
            com_status_var.set("Connected")

    except Exception as e:
        messagebox.showerror("Connection Failed", str(e))

def disconnect_device(device_key: str):
    inst = devices[device_key]["inst"]

    try:
        if devices[device_key]["connected"] and inst is not None:
            try:
                if device_key in ("usb", "eth"):
                    tsp_write(inst, "smua.source.output = smua.OUTPUT_OFF")
                    tsp_write(inst, "smub.source.output = smub.OUTPUT_OFF")
                else:
                    scpi_write(inst, ":OUTP OFF")
            except Exception:
                pass
            inst.close()
    except Exception:
        pass
    finally:
        devices[device_key]["inst"] = None
        devices[device_key]["connected"] = False

        if device_key == "usb":
            usb_status_var.set("Disconnected")
        elif device_key == "eth":
            eth_status_var.set("Disconnected")
        else:
            com_status_var.set("Disconnected")

        log(f"{devices[device_key]['label']} disconnected")

def disconnect_all_devices():
    disconnect_device("usb")
    disconnect_device("eth")
    disconnect_device("com")

    global rm
    try:
        if rm is not None:
            rm.close()
    except Exception:
        pass
    rm = None

# =========================
# Channel helpers
# =========================
def update_measurement_display(channel: str, v: float, i: float):
    r = float("inf") if abs(i) < K2400_MIN_CURRENT_FOR_RESISTANCE else v / i
    vars_ = channel_vars[channel]
    vars_["meas_v"].set(f"{v:.6f}")
    vars_["meas_i"].set(f"{i:.6e}")
    vars_["meas_r"].set("inf" if r == float("inf") else f"{r:.3f}")

def get_channel_config(channel: str):
    vars_ = channel_vars[channel]
    _, tsp_name = CHANNEL_DEVICE_MAP[channel]

    mode = vars_["mode"].get()
    sweep_type = vars_["sweep_type"].get()
    steps = max(2, int(vars_["steps"].get()))
    sweeps_per_set = max(1, int(vars_["sweeps_per_set"].get()))
    set_repeat_count = max(1, int(vars_["set_repeat_count"].get()))
    set_interval = max(0.0, float(vars_["set_interval"].get()))

    return {
        "name": channel,
        "tsp": tsp_name,
        "mode": mode,
        "sweep_type": sweep_type,
        "manual_voltage": float(vars_["manual_voltage"].get()),
        "sweep_start": float(vars_["sweep_start"].get()),
        "sweep_stop": float(vars_["sweep_stop"].get()),
        "sweep_time": float(vars_["sweep_time"].get()),
        "steps": steps,
        "sweeps_per_set": sweeps_per_set,
        "set_repeat_count": set_repeat_count,
        "set_interval": set_interval,
        "current_limit": float(vars_["current_limit"].get()),
        "source_delay": max(0.0, float(vars_["source_delay"].get())),
    }

def build_voltage_plan(cfg):
    """
    Manual mode:
        one point only.

    Sweep mode has three sweep types:
        Sweep Up   : Vstart -> Vend
        Sweep Down : Vend   -> Vstart
        Dual Sweep : Vstart -> Vend -> Vstart

    IMPORTANT TIMING RULE:
        Sweep Time per Direction (s) is the time for ONE direction only.
        Therefore, if Sweep Time per Direction = 10 s:
            Sweep Up   takes 10 s
            Sweep Down takes 10 s
            Dual Sweep takes 20 s, because up = 10 s and down = 10 s

    Repetition rule:
        one set  = repeat the selected sweep type Sweeps Per Set times
        full run = repeat one set Set Repeat Count times, with Set Interval between sets

    CSV clarity:
        This function also generates per-point metadata so the saved CSV can show
        set number, sweep number, point number, and direction/segment clearly.
    """
    if cfg["mode"] == "Manual":
        return {
            "voltages": [cfg["manual_voltage"]],
            "point_meta": [{
                "sample_index": 1,
                "set_number": 1,
                "sweep_in_set": 1,
                "sweep_global": 1,
                "point_in_sweep": 1,
                "points_per_sweep": 1,
                "direction": "manual",
                "point_in_direction": 1,
                "points_per_direction": 1,
            }],
            "point_delay": 0.0,
            "set_end_indices": [],
            "set_interval": 0.0,
        }

    steps = max(2, cfg["steps"])
    start = cfg["sweep_start"]
    stop = cfg["sweep_stop"]
    sweep_time_one_direction = max(0.001, cfg["sweep_time"])
    sweeps_per_set = max(1, cfg["sweeps_per_set"])
    set_repeat_count = max(1, cfg["set_repeat_count"])
    set_interval = max(0.0, cfg["set_interval"])
    sweep_type = cfg.get("sweep_type", "Dual Sweep")

    forward = [start + (stop - start) * i / (steps - 1) for i in range(steps)]
    backward_full = [stop + (start - stop) * i / (steps - 1) for i in range(steps)]

    def build_one_sweep():
        values = []
        meta = []

        if sweep_type == "Sweep Up":
            for i, v in enumerate(forward):
                values.append(v)
                meta.append({
                    "direction": "up",
                    "point_in_direction": i + 1,
                    "points_per_direction": steps,
                })

        elif sweep_type == "Sweep Down":
            for i, v in enumerate(backward_full):
                values.append(v)
                meta.append({
                    "direction": "down",
                    "point_in_direction": i + 1,
                    "points_per_direction": steps,
                })

        else:
            # Dual sweep: include Vstart -> Vend, then Vend -> Vstart.
            # Do not duplicate Vend, because it is already the end of the up segment.
            for i, v in enumerate(forward):
                values.append(v)
                meta.append({
                    "direction": "up",
                    "point_in_direction": i + 1,
                    "points_per_direction": steps,
                })
            for i, v in enumerate(backward_full[1:], start=2):
                values.append(v)
                meta.append({
                    "direction": "down",
                    "point_in_direction": i,
                    "points_per_direction": steps,
                })

        return values, meta

    one_sweep_values, one_sweep_meta = build_one_sweep()
    points_per_sweep = len(one_sweep_values)

    voltages = []
    point_meta = []
    set_end_indices = []
    sample_index = 0

    for set_idx in range(set_repeat_count):
        set_number = set_idx + 1
        for sweep_idx in range(sweeps_per_set):
            sweep_in_set = sweep_idx + 1
            sweep_global = set_idx * sweeps_per_set + sweep_idx + 1

            for point_idx, (v, m) in enumerate(zip(one_sweep_values, one_sweep_meta), start=1):
                sample_index += 1
                voltages.append(v)
                point_meta.append({
                    "sample_index": sample_index,
                    "set_number": set_number,
                    "sweep_in_set": sweep_in_set,
                    "sweep_global": sweep_global,
                    "point_in_sweep": point_idx,
                    "points_per_sweep": points_per_sweep,
                    "direction": m["direction"],
                    "point_in_direction": m["point_in_direction"],
                    "points_per_direction": m["points_per_direction"],
                })

        if set_idx < set_repeat_count - 1:
            set_end_indices.append(len(voltages) - 1)

    # Sweep Time is per single direction. There are (steps - 1) intervals per direction.
    point_delay = sweep_time_one_direction / max(1, steps - 1)

    return {
        "voltages": voltages,
        "point_meta": point_meta,
        "point_delay": point_delay,
        "set_end_indices": set_end_indices,
        "set_interval": set_interval,
    }
def set_output(channel: str, on: bool):
    if not is_channel_connected(channel):
        messagebox.showerror("Error", f"Channel {channel} instrument is not connected.")
        return

    inst = get_inst_for_channel(channel)
    try:
        if is_2400_channel(channel):
            set_2400_output(inst, on)
        else:
            _, tsp_name = CHANNEL_DEVICE_MAP[channel]
            state = f"{tsp_name}.OUTPUT_ON" if on else f"{tsp_name}.OUTPUT_OFF"
            tsp_write(inst, f"{tsp_name}.source.output = {state}")
        log(f"Channel {channel} output {'ON' if on else 'OFF'}")
    except Exception as e:
        messagebox.showerror("Output Control Failed", str(e))

def apply_manual(channel: str):
    if not is_channel_connected(channel):
        messagebox.showerror("Error", f"Channel {channel} instrument is not connected.")
        return

    try:
        cfg = get_channel_config(channel)
        inst = get_inst_for_channel(channel)

        if is_2400_channel(channel):
            configure_2400_voltage_mode(inst, cfg["manual_voltage"], cfg["current_limit"])
            scpi_write(inst, ":OUTP ON")
            time.sleep(max(0.0, cfg["source_delay"]))
            mv, mi = measure_2400(inst)
        else:
            tsp_write(inst, f"{cfg['tsp']}.source.limiti = {cfg['current_limit']}")
            tsp_write(inst, f"{cfg['tsp']}.source.levelv = {cfg['manual_voltage']}")
            time.sleep(max(0.0, cfg["source_delay"]))
            mv = tsp_query_float(inst, f"{cfg['tsp']}.measure.v()")
            mi = tsp_query_float(inst, f"{cfg['tsp']}.measure.i()")

        update_measurement_display(channel, mv, mi)
        log(f"Channel {channel} manual set: {cfg['manual_voltage']:.6f} V, measured I={mi:.6e} A")
    except Exception as e:
        messagebox.showerror("Manual Apply Failed", str(e))

def pause_channel(channel: str):
    if not paused[channel]:
        paused[channel] = True
        pause_started[channel] = time.time()
        log(f"Channel {channel} paused")

def resume_channel(channel: str):
    if paused[channel]:
        if pause_started[channel] is not None:
            paused_accum[channel] += time.time() - pause_started[channel]
        pause_started[channel] = None
        paused[channel] = False
        log(f"Channel {channel} resumed")

def turn_off_channels_for_device(device_key, channels):
    for ch in channels:
        try:
            inst = get_inst_for_channel(ch)
            if inst is None:
                continue
            if device_key == "com":
                scpi_write(inst, ":OUTP OFF")
            else:
                _, tsp_name = CHANNEL_DEVICE_MAP[ch]
                tsp_write(inst, f"{tsp_name}.source.output = {tsp_name}.OUTPUT_OFF")
        except Exception:
            pass

# =========================
# 3 producer threads
# =========================
def producer_run_for_device(device_key: str):
    q = QUEUE_MAP[device_key]
    channels = [ch for ch in DEVICE_CHANNELS[device_key] if is_channel_connected(ch)]

    if not channels:
        producer_done[device_key] = True
        q.put({"type": "finished", "device": device_key})
        return

    try:
        cfgs = {ch: get_channel_config(ch) for ch in channels}
        insts = {ch: get_inst_for_channel(ch) for ch in channels}

        voltage_lists = {}
        point_meta_lists = {}
        delays = {}
        set_end_indices = {}
        set_intervals = {}

        waiting_until = {}
        completed_set_indices = {}
        next_point_time = {}
        completed = {}
        idx = {}

        t0 = run_start_time

        for ch in channels:
            cfg = cfgs[ch]
            inst = insts[ch]
            plan = build_voltage_plan(cfg)

            voltage_lists[ch] = plan["voltages"]
            point_meta_lists[ch] = plan["point_meta"]
            delays[ch] = plan["point_delay"]
            set_end_indices[ch] = set(plan["set_end_indices"])
            set_intervals[ch] = plan["set_interval"]

            waiting_until[ch] = None
            completed_set_indices[ch] = set()
            completed[ch] = False
            idx[ch] = 0

            # Absolute schedule for the first point.
            # After each measured point, this advances by point_delay.
            # This prevents timing drift when many sweeps/sets are used.
            next_point_time[ch] = time.time()

            if device_key == "com":
                configure_2400_voltage_mode(inst, voltage_lists[ch][0], cfg["current_limit"])
                scpi_write(inst, ":OUTP ON")
            else:
                tsp_write(inst, f"{cfg['tsp']}.source.limiti = {cfg['current_limit']}")
                tsp_write(inst, f"{cfg['tsp']}.source.output = {cfg['tsp']}.OUTPUT_ON")
                tsp_write(inst, f"{cfg['tsp']}.source.levelv = {voltage_lists[ch][0]}")

        q.put({"type": "status", "device": device_key, "message": f"{device_key.upper()} producer started"})

        while True:
            if stop_requested:
                q.put({"type": "status", "device": device_key, "message": f"{device_key.upper()} producer stopped by user"})
                break

            now = time.time()
            done_flags = []
            active_channels_this_cycle = []

            # Source-update phase.
            # The sweep schedule is based on next_point_time[ch], not on source_delay.
            # source_delay is only used as settle time after setting the voltage.
            for ch in channels:
                cfg = cfgs[ch]
                inst = insts[ch]

                if completed[ch]:
                    done_flags.append(True)
                    continue

                if paused[ch]:
                    done_flags.append(False)
                    continue

                # Between-set interval: hold the previous set-ending voltage.
                # Do not source a new point and do not measure while waiting.
                if waiting_until[ch] is not None:
                    if now < waiting_until[ch]:
                        done_flags.append(False)
                        continue

                    # Interval finished. Advance to the first point of the next set.
                    waiting_until[ch] = None
                    idx[ch] = min(idx[ch] + 1, len(voltage_lists[ch]) - 1)

                    # Restart the point schedule from now for the new set.
                    # This avoids carrying timing error from the previous set.
                    next_point_time[ch] = time.time()

                    q.put({
                        "type": "status",
                        "device": device_key,
                        "message": f"Channel {ch} starting next set automatically."
                    })

                # Absolute point scheduling.
                # If the next point is not due yet, skip this channel this cycle.
                if cfg["mode"] == "Sweep" and now < next_point_time[ch]:
                    done_flags.append(False)
                    continue

                set_v = voltage_lists[ch][idx[ch]]

                if device_key == "com":
                    configure_2400_voltage_mode(inst, set_v, cfg["current_limit"])
                else:
                    tsp_write(inst, f"{cfg['tsp']}.source.levelv = {set_v}")

                active_channels_this_cycle.append(ch)

            if not active_channels_this_cycle:
                # All channels are completed, paused, waiting between sets, or waiting
                # for their next scheduled point. Keep producer responsive to Stop Run.
                time.sleep(0.002)
                continue

            max_delay = max(cfgs[ch]["source_delay"] for ch in active_channels_this_cycle)
            time.sleep(max(0.0, max_delay))

            # Measurement phase. Measure only channels that were actively sourced above.
            for ch in active_channels_this_cycle:
                cfg = cfgs[ch]
                inst = insts[ch]

                if stop_requested:
                    done_flags.append(False)
                    continue

                if paused[ch]:
                    done_flags.append(False)
                    continue

                if waiting_until[ch] is not None:
                    done_flags.append(False)
                    continue

                set_v = voltage_lists[ch][idx[ch]]

                if device_key == "com":
                    mv, mi = measure_2400(inst)
                else:
                    mv = tsp_query_float(inst, f"{cfg['tsp']}.measure.v()")
                    mi = tsp_query_float(inst, f"{cfg['tsp']}.measure.i()")

                measure_time = time.time()
                elapsed_total = measure_time - t0
                point_meta = point_meta_lists[ch][idx[ch]]

                q.put({
                    "type": "data",
                    "device": device_key,
                    "channel": ch,
                    "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f"),
                    "elapsed_time_s": elapsed_total,
                    "mode": cfg["mode"],
                    "sweep_type": cfg.get("sweep_type", ""),
                    "sweeps_per_set": cfg.get("sweeps_per_set", 1),
                    "set_repeat_count": cfg.get("set_repeat_count", 1),
                    "set_interval_s": cfg.get("set_interval", 0.0),
                    "paused": paused[ch],
                    "source_delay_s": cfg["source_delay"],
                    "point_delay_s": delays[ch],
                    "sample_index": point_meta.get("sample_index", ""),
                    "set_number": point_meta.get("set_number", ""),
                    "sweep_in_set": point_meta.get("sweep_in_set", ""),
                    "sweep_global": point_meta.get("sweep_global", ""),
                    "point_in_sweep": point_meta.get("point_in_sweep", ""),
                    "points_per_sweep": point_meta.get("points_per_sweep", ""),
                    "direction": point_meta.get("direction", ""),
                    "point_in_direction": point_meta.get("point_in_direction", ""),
                    "points_per_direction": point_meta.get("points_per_direction", ""),
                    "set_voltage_V": set_v,
                    "measured_voltage_V": mv,
                    "measured_current_A": mi,
                })

                done = (cfg["mode"] == "Manual") or (idx[ch] >= len(voltage_lists[ch]) - 1)

                # End of one set, but not end of the full run.
                # Start the set interval only once for this set-end index.
                if (
                    not done
                    and cfg["mode"] == "Sweep"
                    and idx[ch] in set_end_indices[ch]
                    and idx[ch] not in completed_set_indices[ch]
                ):
                    completed_set_indices[ch].add(idx[ch])
                    wait_s = set_intervals[ch]
                    waiting_until[ch] = time.time() + wait_s

                    q.put({
                        "type": "status",
                        "device": device_key,
                        "message": (
                            f"Channel {ch} completed one set "
                            f"({cfg['sweeps_per_set']} {cfg.get('sweep_type', 'sweep')} sweeps). "
                            f"Holding at {set_v:.6f} V for {wait_s:.3f} s before next set."
                        )
                    })

                    done_flags.append(False)
                    continue

                if done:
                    completed[ch] = True
                    done_flags.append(True)
                    continue

                # Advance to the next voltage point.
                idx[ch] = min(idx[ch] + 1, len(voltage_lists[ch]) - 1)

                # Absolute schedule update.
                # Do NOT use time.time() + delay here; that would accumulate drift.
                # Advancing from the previous target time keeps the intended sweep rate.
                if cfg["mode"] == "Sweep":
                    next_point_time[ch] += delays[ch]

                    # If the instrument communication was slower than the requested
                    # point interval, do not try to sleep negative time. Continue ASAP.
                    if next_point_time[ch] < time.time():
                        next_point_time[ch] = time.time()

                done_flags.append(False)

            # For channels not active this cycle, preserve not-done/done state.
            inactive_channels = set(channels) - set(active_channels_this_cycle)
            for ch in inactive_channels:
                if completed[ch]:
                    done_flags.append(True)
                elif not paused[ch] and waiting_until[ch] is None:
                    done = (cfgs[ch]["mode"] == "Manual") or (idx[ch] >= len(voltage_lists[ch]) - 1)
                    if done:
                        completed[ch] = True
                    done_flags.append(done)

            if channels and all(done_flags):
                q.put({"type": "status", "device": device_key, "message": f"{device_key.upper()} producer completed"})
                break

            time.sleep(0.001)

    except Exception as e:
        q.put({"type": "error", "device": device_key, "message": str(e)})

    finally:
        turn_off_channels_for_device(device_key, channels)
        for ch in channels:
            q.put({"type": "status", "device": device_key, "message": f"Channel {ch} output OFF automatically"})
        producer_done[device_key] = True
        q.put({"type": "finished", "device": device_key})


# =========================
# Consumer
# =========================
def drain_one_queue(q):
    items = []
    while True:
        try:
            items.append(q.get_nowait())
        except queue.Empty:
            break
    return items

def all_active_producers_finished():
    active_device_keys = [dk for dk, chans in DEVICE_CHANNELS.items() if any(is_channel_connected(ch) for ch in chans)]
    return all(producer_done[dk] for dk in active_device_keys)

def drain_all_queues():
    global consumer_tick_count
    consumer_tick_count += 1

    items = []
    items.extend(drain_one_queue(usb_queue))
    items.extend(drain_one_queue(eth_queue))
    items.extend(drain_one_queue(com_queue))

    last_log_lines = []
    got_data = False

    for item in items:
        if item["type"] == "data":
            got_data = True
            ch = item["channel"]
            mv = item["measured_voltage_V"]
            mi = item["measured_current_A"]

            update_measurement_display(ch, mv, mi)
            plot_data[f"{ch}_v"].append(mv)
            plot_data[f"{ch}_i"].append(mi)
            rows_buffer.append(item)

            last_log_lines.append(
                f"{ch} t={item['elapsed_time_s']:7.3f}s "
                f"set={item['set_voltage_V']:.5f} V "
                f"I={mi:.6e} A paused={item['paused']}"
            )

        elif item["type"] == "status":
            log(item["message"])

        elif item["type"] == "error":
            messagebox.showerror("Run Error", item["message"])

    if got_data and consumer_tick_count % PLOT_REFRESH_EVERY == 0:
        refresh_plot_main_thread()

    if last_log_lines and consumer_tick_count % LOG_REFRESH_EVERY == 0:
        log(" | ".join(last_log_lines[-3:]))

    if all_active_producers_finished():
        finalize_run_outputs()
        return

    root.after(UI_POLL_MS, drain_all_queues)

def finalize_run_outputs():
    """Start slow file saving in a low-priority background thread.

    Measurement producers are already finished when this function is called, but CSV
    formatting and PNG saving can still be slow. Running them in a separate daemon
    thread keeps the Tkinter UI responsive and keeps this work lower priority than
    the critical instrument-control path.
    """
    global save_output_started

    if save_output_started:
        return

    if not current_run_paths["csv"] or not current_run_paths["png"]:
        return

    save_output_started = True

    rows_snapshot = list(rows_buffer)
    plot_snapshot = {key: list(values) for key, values in plot_data.items()}
    paths_snapshot = dict(current_run_paths)

    log("Measurement finished. CSV/plot saving started in low-priority background thread.")

    t = threading.Thread(
        target=save_outputs_worker,
        args=(rows_snapshot, plot_snapshot, paths_snapshot),
        daemon=True,
    )
    t.start()
    root.after(100, poll_save_status_queue)


def poll_save_status_queue():
    while True:
        try:
            item = save_status_queue.get_nowait()
        except queue.Empty:
            break

        if item["type"] == "status":
            log(item["message"])
        elif item["type"] == "error":
            messagebox.showerror("Save Error", item["message"])

    # Keep polling while the save has started and at least one save worker may still report.
    # The polling itself is tiny and does not touch the producer timing path.
    if save_output_started:
        root.after(300, poll_save_status_queue)


def save_plot_file_from_snapshot(png_path: str, plot_snapshot: dict):
    fig = Figure(figsize=(10, 6))
    FigureCanvasAgg(fig)
    ax = fig.add_subplot(111)

    any_data = False
    styles = {
        "A": ("o", "-", "Channel A"),
        "B": ("x", "--", "Channel B"),
        "C": ("s", "-.", "Channel C"),
        "D": ("^", ":", "Channel D"),
        "E": ("d", "-", "Channel E / 2400"),
    }

    for ch in CHANNEL_ORDER:
        if plot_snapshot.get(f"{ch}_v"):
            marker, linestyle, label = styles[ch]
            ax.plot(
                plot_snapshot[f"{ch}_v"],
                plot_snapshot[f"{ch}_i"],
                marker=marker,
                linestyle=linestyle,
                label=label,
            )
            any_data = True

    ax.set_xlabel("Voltage (V)")
    ax.set_ylabel("Current (A)")
    ax.set_title("Keithley Real-Time I-V Plot")
    ax.grid(True)
    if any_data:
        ax.legend()
    fig.tight_layout()
    fig.savefig(png_path, dpi=150)


def save_outputs_worker(rows_snapshot, plot_snapshot, paths_snapshot):
    try:
        # Be polite to the critical path and UI scheduler. The producers should be done,
        # but this keeps saving as a low-priority task in practice.
        time.sleep(0.05)

        csv_path = paths_snapshot["csv"]
        png_path = paths_snapshot["png"]

        fieldnames = ["timestamp", "elapsed_time_s"]
        per_channel_fields = [
            "mode",
            "sweep_type",
            "sweeps_per_set",
            "set_repeat_count",
            "set_interval_s",
            "sample_index",
            "set_number",
            "sweep_in_set",
            "sweep_global",
            "point_in_sweep",
            "points_per_sweep",
            "direction",
            "point_in_direction",
            "points_per_direction",
            "paused",
            "source_delay_s",
            "point_delay_s",
            "set_voltage_V",
            "measured_voltage_V",
            "measured_current_A",
        ]

        for ch in CHANNEL_ORDER:
            fieldnames.extend([f"{ch}_{field}" for field in per_channel_fields])

        csv_rows = []
        grouped = {}

        for row in rows_snapshot:
            ts = row["timestamp"]
            if ts not in grouped:
                grouped[ts] = {
                    "timestamp": ts,
                    "elapsed_time_s": row["elapsed_time_s"],
                }

            ch = row["channel"]
            grouped[ts][f"{ch}_mode"] = row.get("mode", "")
            grouped[ts][f"{ch}_sweep_type"] = row.get("sweep_type", "")
            grouped[ts][f"{ch}_sweeps_per_set"] = row.get("sweeps_per_set", "")
            grouped[ts][f"{ch}_set_repeat_count"] = row.get("set_repeat_count", "")
            grouped[ts][f"{ch}_set_interval_s"] = row.get("set_interval_s", "")
            grouped[ts][f"{ch}_sample_index"] = row.get("sample_index", "")
            grouped[ts][f"{ch}_set_number"] = row.get("set_number", "")
            grouped[ts][f"{ch}_sweep_in_set"] = row.get("sweep_in_set", "")
            grouped[ts][f"{ch}_sweep_global"] = row.get("sweep_global", "")
            grouped[ts][f"{ch}_point_in_sweep"] = row.get("point_in_sweep", "")
            grouped[ts][f"{ch}_points_per_sweep"] = row.get("points_per_sweep", "")
            grouped[ts][f"{ch}_direction"] = row.get("direction", "")
            grouped[ts][f"{ch}_point_in_direction"] = row.get("point_in_direction", "")
            grouped[ts][f"{ch}_points_per_direction"] = row.get("points_per_direction", "")
            grouped[ts][f"{ch}_paused"] = row.get("paused", "")
            grouped[ts][f"{ch}_source_delay_s"] = row.get("source_delay_s", "")
            grouped[ts][f"{ch}_point_delay_s"] = row.get("point_delay_s", "")
            grouped[ts][f"{ch}_set_voltage_V"] = row.get("set_voltage_V", "")
            grouped[ts][f"{ch}_measured_voltage_V"] = row.get("measured_voltage_V", "")
            grouped[ts][f"{ch}_measured_current_A"] = row.get("measured_current_A", "")

        for _, row in grouped.items():
            for ch in CHANNEL_ORDER:
                for field in per_channel_fields:
                    row.setdefault(f"{ch}_{field}", "")
            csv_rows.append(row)

        csv_rows.sort(key=lambda x: x["elapsed_time_s"])

        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(csv_rows)

        # Give the UI a chance before heavier PNG rendering.
        time.sleep(0.05)
        save_plot_file_from_snapshot(png_path, plot_snapshot)

        save_status_queue.put({"type": "status", "message": f"CSV saved: {csv_path}"})
        save_status_queue.put({"type": "status", "message": f"Plot saved: {png_path}"})
        save_status_queue.put({"type": "status", "message": "Low-priority save task completed."})

    except Exception as e:
        save_status_queue.put({"type": "error", "message": str(e)})
# =========================
# Run control
# =========================
def clear_all_queues():
    for q in [usb_queue, eth_queue, com_queue]:
        while not q.empty():
            try:
                q.get_nowait()
            except queue.Empty:
                break

def start_run():
    global stop_requested, plot_initialized, plot_window_opened
    global rows_buffer, consumer_tick_count, run_start_time, producer_threads, producer_done
    global save_output_started

    if any(t.is_alive() for t in producer_threads.values()):
        messagebox.showwarning("Warning", "A run is already in progress.")
        return

    active_channels = [ch for ch in CHANNEL_ORDER if is_channel_connected(ch)]
    if not active_channels:
        messagebox.showerror("Error", "Connect at least one instrument first.")
        return

    base_name = sanitize_filename(save_name_var.get())
    if not base_name:
        messagebox.showerror("Error", "Please type a file name in the Save Name box.")
        return

    try:
        for ch in active_channels:
            get_channel_config(ch)
    except Exception as e:
        messagebox.showerror("Invalid Input", str(e))
        return

    clear_all_queues()
    save_output_started = False
    while not save_status_queue.empty():
        try:
            save_status_queue.get_nowait()
        except queue.Empty:
            break
    rows_buffer = []
    consumer_tick_count = 0
    clear_plot_data()

    plot_initialized = False
    plot_window_opened = False
    init_plot_window()

    for ch in CHANNEL_ORDER:
        paused[ch] = False
        pause_started[ch] = None
        paused_accum[ch] = 0.0

    stop_requested = False
    run_start_time = time.time()

    base_path = make_unique_base_path(base_name)
    current_run_paths["csv"] = base_path + ".csv"
    current_run_paths["png"] = base_path + ".png"

    producer_done = {"usb": False, "eth": False, "com": False}
    producer_threads = {}

    for device_key in ["usb", "eth", "com"]:
        has_active = any(is_channel_connected(ch) for ch in DEVICE_CHANNELS[device_key])
        if has_active:
            t = threading.Thread(target=producer_run_for_device, args=(device_key,), daemon=True)
            producer_threads[device_key] = t
            t.start()
        else:
            producer_done[device_key] = True

    root.after(UI_POLL_MS, drain_all_queues)

def stop_run():
    global stop_requested
    stop_requested = True
    log("Stop requested")

# =========================
# GUI builders
# =========================
def build_connection_frame(parent):
    frame = ttk.LabelFrame(parent, text="Connections")
    frame.pack(fill="x", padx=10, pady=8)

    ttk.Label(frame, text="USB VISA Resource (A/B):").grid(row=0, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=usb_resource_var, width=45).grid(row=0, column=1, padx=6, pady=6, sticky="w")
    ttk.Button(frame, text="Connect USB", command=lambda: connect_device("usb")).grid(row=0, column=2, padx=6, pady=6)
    ttk.Button(frame, text="Disconnect USB", command=lambda: disconnect_device("usb")).grid(row=0, column=3, padx=6, pady=6)
    ttk.Label(frame, text="Status:").grid(row=0, column=4, padx=6, pady=6)
    ttk.Label(frame, textvariable=usb_status_var).grid(row=0, column=5, padx=6, pady=6)

    ttk.Label(frame, text="Ethernet VISA Resource (C/D):").grid(row=1, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=eth_resource_var, width=45).grid(row=1, column=1, padx=6, pady=6, sticky="w")
    ttk.Button(frame, text="Connect Ethernet", command=lambda: connect_device("eth")).grid(row=1, column=2, padx=6, pady=6)
    ttk.Button(frame, text="Disconnect Ethernet", command=lambda: disconnect_device("eth")).grid(row=1, column=3, padx=6, pady=6)
    ttk.Label(frame, text="Status:").grid(row=1, column=4, padx=6, pady=6)
    ttk.Label(frame, textvariable=eth_status_var).grid(row=1, column=5, padx=6, pady=6)

    ttk.Label(frame, text="COM VISA Resource (E / 2400):").grid(row=2, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=com_resource_var, width=45).grid(row=2, column=1, padx=6, pady=6, sticky="w")
    ttk.Button(frame, text="Connect COM", command=lambda: connect_device("com")).grid(row=2, column=2, padx=6, pady=6)
    ttk.Button(frame, text="Disconnect COM", command=lambda: disconnect_device("com")).grid(row=2, column=3, padx=6, pady=6)
    ttk.Label(frame, text="Status:").grid(row=2, column=4, padx=6, pady=6)
    ttk.Label(frame, textvariable=com_status_var).grid(row=2, column=5, padx=6, pady=6)

def build_channel_panel(parent, channel, title, row, col):
    frame = ttk.LabelFrame(parent, text=title)
    frame.grid(row=row, column=col, padx=8, pady=8, sticky="nsew")

    vars_ = channel_vars[channel]
    r = 0

    ttk.Label(frame, text="Mode").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Combobox(frame, textvariable=vars_["mode"], values=["Manual", "Sweep"], width=12, state="readonly").grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Sweep Type").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Combobox(
        frame,
        textvariable=vars_["sweep_type"],
        values=["Sweep Up", "Sweep Down", "Dual Sweep"],
        width=14,
        state="readonly",
    ).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Manual Voltage (V)").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=vars_["manual_voltage"], width=14).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Sweep Start (V)").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=vars_["sweep_start"], width=14).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Sweep Stop (V)").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=vars_["sweep_stop"], width=14).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Sweep Time per Direction (s)").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=vars_["sweep_time"], width=14).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Sweep Steps").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=vars_["steps"], width=14).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Sweeps Per Set").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=vars_["sweeps_per_set"], width=14).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Set Repeat Count").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=vars_["set_repeat_count"], width=14).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Set Interval (s)").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=vars_["set_interval"], width=14).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Current Limit (A)").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=vars_["current_limit"], width=14).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Source→Measure Delay (s)").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Entry(frame, textvariable=vars_["source_delay"], width=14).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Button(frame, text="Apply Manual", command=lambda c=channel: apply_manual(c)).grid(row=r, column=0, padx=6, pady=8)
    ttk.Button(frame, text="Output ON", command=lambda c=channel: set_output(c, True)).grid(row=r, column=1, padx=6, pady=8)
    ttk.Button(frame, text="Output OFF", command=lambda c=channel: set_output(c, False)).grid(row=r, column=2, padx=6, pady=8)
    r += 1

    ttk.Button(frame, text="Pause", command=lambda c=channel: pause_channel(c)).grid(row=r, column=0, padx=6, pady=8)
    ttk.Button(frame, text="Resume", command=lambda c=channel: resume_channel(c)).grid(row=r, column=1, padx=6, pady=8)
    r += 1

    ttk.Label(frame, text="Measured V (V)").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Label(frame, textvariable=vars_["meas_v"]).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Measured I (A)").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Label(frame, textvariable=vars_["meas_i"]).grid(row=r, column=1, padx=6, pady=6, sticky="w")
    r += 1

    ttk.Label(frame, text="Measured R (Ohm)").grid(row=r, column=0, padx=6, pady=6, sticky="w")
    ttk.Label(frame, textvariable=vars_["meas_r"]).grid(row=r, column=1, padx=6, pady=6, sticky="w")

# =========================
# GUI
# =========================
root = tk.Tk()
root.title("Keithley Multi-Channel GUI - Sweep Modes")
root.geometry("1200x900")

outer_frame = ttk.Frame(root)
outer_frame.pack(fill="both", expand=True)

canvas = tk.Canvas(outer_frame)
v_scrollbar = ttk.Scrollbar(outer_frame, orient="vertical", command=canvas.yview)
h_scrollbar = ttk.Scrollbar(outer_frame, orient="horizontal", command=canvas.xview)

canvas.configure(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)

v_scrollbar.pack(side="right", fill="y")
h_scrollbar.pack(side="bottom", fill="x")
canvas.pack(side="left", fill="both", expand=True)

main_frame = ttk.Frame(canvas)
canvas_window = canvas.create_window((0, 0), window=main_frame, anchor="nw")

def on_main_frame_configure(event=None):
    canvas.configure(scrollregion=canvas.bbox("all"))

def on_canvas_configure(event):
    canvas.itemconfig(canvas_window, width=event.width)

main_frame.bind("<Configure>", on_main_frame_configure)
canvas.bind("<Configure>", on_canvas_configure)

def _on_mousewheel(event):
    canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

def _on_shift_mousewheel(event):
    canvas.xview_scroll(int(-1 * (event.delta / 120)), "units")

canvas.bind_all("<MouseWheel>", _on_mousewheel)
canvas.bind_all("<Shift-MouseWheel>", _on_shift_mousewheel)

usb_resource_var = tk.StringVar(value=USB_RESOURCE_DEFAULT)
eth_resource_var = tk.StringVar(value=ETH_RESOURCE_DEFAULT)
com_resource_var = tk.StringVar(value=COM_RESOURCE_DEFAULT)

usb_status_var = tk.StringVar(value="Disconnected")
eth_status_var = tk.StringVar(value="Disconnected")
com_status_var = tk.StringVar(value="Disconnected")
save_name_var = tk.StringVar(value="run_01")

defaults = {
    "A": {"manual_voltage": "0.01"},
    "B": {"manual_voltage": "0.02"},
    "C": {"manual_voltage": "0.01"},
    "D": {"manual_voltage": "0.02"},
    "E": {"manual_voltage": "0.01"},
}

for ch in CHANNEL_ORDER:
    channel_vars[ch] = {
        "mode": tk.StringVar(value="Manual"),
        "sweep_type": tk.StringVar(value="Dual Sweep"),
        "manual_voltage": tk.StringVar(value=defaults[ch]["manual_voltage"]),
        "sweep_start": tk.StringVar(value="0"),
        "sweep_stop": tk.StringVar(value="0.1"),
        "sweep_time": tk.StringVar(value="10"),
        "steps": tk.StringVar(value="100"),
        "sweeps_per_set": tk.StringVar(value="5"),
        "set_repeat_count": tk.StringVar(value="1"),
        "set_interval": tk.StringVar(value="0"),
        "current_limit": tk.StringVar(value="0.001"),
        "source_delay": tk.StringVar(value="0.05"),
        "meas_v": tk.StringVar(value="-"),
        "meas_i": tk.StringVar(value="-"),
        "meas_r": tk.StringVar(value="-"),
    }

build_connection_frame(main_frame)

channels_frame = ttk.Frame(main_frame)
channels_frame.pack(fill="x", padx=10, pady=4)

for i in range(3):
    channels_frame.columnconfigure(i, weight=1)
for i in range(2):
    channels_frame.rowconfigure(i, weight=1)

build_channel_panel(channels_frame, "A", "Channel A / USB smua", 0, 0)
build_channel_panel(channels_frame, "B", "Channel B / USB smub", 0, 1)
build_channel_panel(channels_frame, "C", "Channel C / Ethernet smua", 0, 2)
build_channel_panel(channels_frame, "D", "Channel D / Ethernet smub", 1, 0)
build_channel_panel(channels_frame, "E", "Channel E / Keithley 2400", 1, 1)

run_frame = ttk.LabelFrame(main_frame, text="Run Control")
run_frame.pack(fill="x", padx=10, pady=8)

ttk.Label(run_frame, text="Save Name:").grid(row=0, column=0, padx=8, pady=8, sticky="w")
ttk.Entry(run_frame, textvariable=save_name_var, width=30).grid(row=0, column=1, padx=8, pady=8, sticky="w")
ttk.Button(run_frame, text="Start Run", command=start_run).grid(row=0, column=2, padx=8, pady=8)
ttk.Button(run_frame, text="Stop Run", command=stop_run).grid(row=0, column=3, padx=8, pady=8)

ttk.Label(run_frame, text=f"Files will be saved in: {SAVE_DIR}").grid(
    row=1, column=0, columnspan=4, padx=8, pady=4, sticky="w"
)

log_frame = ttk.LabelFrame(main_frame, text="Log")
log_frame.pack(fill="both", expand=True, padx=10, pady=8)

log_text = tk.Text(log_frame, height=16)
log_text.pack(fill="both", expand=True, padx=6, pady=6)

def on_close():
    stop_run()
    disconnect_all_devices()
    root.destroy()

root.protocol("WM_DELETE_WINDOW", on_close)
root.mainloop()