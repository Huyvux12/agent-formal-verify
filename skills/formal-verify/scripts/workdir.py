#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Manage temporary verification workdirs, signal cleanup, and storage preflight checks."""
from __future__ import annotations

import os
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path

GIB = 1024**3
DEFAULT_PREFLIGHT_MIN_GIB = 64
DEFAULT_RUNTIME_MIN_GIB = 10
SKIP_MOUNT_PREFIXES = (
    "/dev",
    "/proc",
    "/sys",
    "/run",
    "/System/",
    "/Volumes/.timemachine",
    "/Volumes/Recovery",
)


class SignalTerminated(BaseException):
    """Raised on SIGINT or SIGTERM so context managers and finally blocks still clean up."""

    def __init__(self, signum):
        self.signum = signum
        self.status = 128 + signum
        super().__init__(f"terminated by signal {signum}")


def ensure_temp_root():
    """Ensure TMPDIR exists when set so tempfile does not silently fall back to the system disk."""
    configured = os.environ.get("TMPDIR", "").strip()
    if configured:
        try:
            Path(configured).mkdir(parents=True, exist_ok=True)
        except OSError:
            pass
    return Path(tempfile.gettempdir()).resolve()


@contextmanager
def signal_cleanup():
    """Convert SIGINT/SIGTERM into SignalTerminated while running on the main thread."""
    if threading.current_thread() is not threading.main_thread():
        yield
        return
    state = {"caught": False}
    previous = {}

    def handle(signum, _frame):
        if state["caught"]:
            return
        state["caught"] = True
        raise SignalTerminated(signum)

    for signum in (signal.SIGINT, signal.SIGTERM):
        previous[signum] = signal.getsignal(signum)
        signal.signal(signum, handle)
    try:
        yield
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def stop_process_group(process):
    """Terminate a spawned subprocess and its POSIX process group cleanly."""
    if process.poll() is not None:
        return
    try:
        if os.name == "posix":
            os.killpg(process.pid, signal.SIGTERM)
        else:
            process.terminate()
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        try:
            if os.name == "posix":
                os.killpg(process.pid, signal.SIGKILL)
            else:
                process.kill()
        except ProcessLookupError:
            pass
        process.wait()


def run_captured(command, **kwargs):
    """Run a command in its own POSIX session and kill its process group on signal or interruption."""
    process = subprocess.Popen(
        command,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=(os.name == "posix"),
        **kwargs,
    )
    try:
        stdout, stderr = process.communicate()
    except BaseException:
        stop_process_group(process)
        raise
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def _min_free_gib(default):
    raw = os.environ.get("FORMAL_MIN_FREE_GIB", "").strip()
    if not raw:
        return default
    if raw.isdigit():
        return int(raw)
    return default


def _skipped_mount(mount):
    if mount == "/":
        return True
    return any(mount == prefix.rstrip("/") or mount.startswith(prefix) for prefix in SKIP_MOUNT_PREFIXES)


def parse_df_mounts(
    df_text,
    temp_root,
    root_path=Path("/"),
    *,
    stat_fn=os.stat,
    access_fn=os.access,
    usage_fn=shutil.disk_usage,
):
    """Return writable local mounted volumes with more free space than temp_root, largest first."""
    temp_free = usage_fn(temp_root).free
    seen_devs = {stat_fn(temp_root).st_dev, stat_fn(root_path).st_dev}
    candidates = {}
    for line in df_text.splitlines()[1:]:
        parts = line.split(None, 5)
        if len(parts) != 6:
            continue
        mount = parts[5].strip()
        if not mount or _skipped_mount(mount):
            continue
        try:
            dev = stat_fn(mount).st_dev
            if dev in seen_devs or not access_fn(mount, os.W_OK):
                continue
            free = usage_fn(mount).free
        except OSError:
            continue
        if free > temp_free:
            existing = candidates.get(dev)
            if existing is None or len(mount) < len(existing[0]):
                candidates[dev] = (mount, free)
    return sorted(candidates.values(), key=lambda item: (-item[1], item[0]))


@dataclass(frozen=True)
class StorageReport:
    temp_root: Path
    temp_free: int
    root_free: int
    same_device: bool
    min_gib: int
    candidates: tuple


def inspect_storage(default_min_gib=DEFAULT_PREFLIGHT_MIN_GIB):
    """Inspect active temporary storage, system root free space, and writable larger local volumes."""
    temp_root = ensure_temp_root()
    root_path = Path("/")
    temp_free = shutil.disk_usage(temp_root).free
    root_free = shutil.disk_usage(root_path).free
    same_device = os.stat(temp_root).st_dev == os.stat(root_path).st_dev
    min_gib = _min_free_gib(default_min_gib)
    candidates = []
    try:
        done = subprocess.run(["df", "-lkP"], capture_output=True, text=True, check=False)
        if done.returncode == 0 and done.stdout:
            candidates = parse_df_mounts(done.stdout, temp_root, root_path)
    except OSError:
        candidates = []
    return StorageReport(temp_root, temp_free, root_free, same_device, min_gib, tuple(candidates))


def format_report(report):
    """Format preflight storage lines for setup.sh and interactive agent checks."""
    lines = [f"TEMP_DIR {report.temp_root} ({report.temp_free / GIB:.1f} GiB free)"]
    if not report.same_device:
        lines.append(f"SYSTEM_DISK / ({report.root_free / GIB:.1f} GiB free)")
    threshold = report.min_gib * GIB
    low_temp = report.min_gib > 0 and report.temp_free < threshold
    low_root = report.min_gib > 0 and report.root_free < threshold
    if low_temp or low_root:
        lines.append(
            f"WARN low free space (< {report.min_gib} GiB): temp dir {report.temp_root} has "
            f"{report.temp_free / GIB:.1f} GiB free, system disk / has {report.root_free / GIB:.1f} GiB free; "
            "TLC disk queues, Kani targets, or Lean builds may exhaust disk space. Set TMPDIR=<dir> to choose another volume."
        )
    for mount, free in report.candidates:
        suggested = Path(mount) / ".tmp" / "formal-verify"
        lines.append(f"EXTERNAL_VOLUME {mount} ({free / GIB:.1f} GiB free; suggested TMPDIR={suggested})")
    return lines


def warn_runtime():
    """Emit a stderr warning before heavy verification runs if active temp storage is critically low."""
    report = inspect_storage(DEFAULT_RUNTIME_MIN_GIB)
    if report.min_gib <= 0:
        return
    threshold = report.min_gib * GIB
    if report.temp_free >= threshold:
        return
    sys.stderr.write(
        f"WARN low free space on temp dir {report.temp_root}: {report.temp_free / GIB:.1f} GiB free "
        f"(< {report.min_gib} GiB); set TMPDIR=<dir> to use another volume.\n"
    )
    for mount, free in report.candidates:
        suggested = Path(mount) / ".tmp" / "formal-verify"
        sys.stderr.write(f"WARN candidate volume {mount} ({free / GIB:.1f} GiB free; suggested TMPDIR={suggested})\n")
    sys.stderr.flush()


def main():
    action = sys.argv[1] if len(sys.argv) == 2 else ""
    if action == "report":
        for line in format_report(inspect_storage()):
            print(line)
        return 0
    if action == "warn":
        warn_runtime()
        return 0
    print("usage: workdir.py <report|warn>", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
