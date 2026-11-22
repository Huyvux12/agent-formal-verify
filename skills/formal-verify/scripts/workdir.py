#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Manage temporary verification workdirs, signal cleanup, and storage preflight checks."""
from __future__ import annotations

import os
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
from contextlib import contextmanager, suppress
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
    "/System",
    "/Volumes/.timemachine",
    "/Volumes/Recovery",
)

_warned_runtime = False


class TempDirError(Exception):
    """Raised when an explicitly set TMPDIR cannot be created or written."""


class SignalTerminated(BaseException):
    """Raised on handled termination signals so context managers and finally blocks still clean up."""

    def __init__(self, signum):
        self.signum = signum
        self.status = 128 + signum
        super().__init__(f"terminated by signal {signum}")

    def exit(self):
        """End the process by the signal itself, so a calling shell stops as it would without the cleanup."""
        with suppress(OSError):
            sys.stdout.flush()
            sys.stderr.flush()
        signal.signal(self.signum, signal.SIG_DFL)
        os.kill(os.getpid(), self.signum)
        sys.exit(self.status)


def ensure_temp_root():
    """Ensure explicit TMPDIR exists and is writable so tempfile never silently falls back."""
    configured = os.environ.get("TMPDIR", "").strip()
    if configured:
        path = Path(configured)
        try:
            path.mkdir(parents=True, exist_ok=True)
        except OSError as error:
            raise TempDirError(f"FAIL TMPDIR={configured!r} cannot be created: {error}") from error
        if not path.is_dir() or not os.access(path, os.W_OK):
            raise TempDirError(f"FAIL TMPDIR={configured!r} is not a writable directory")
        return path.resolve()
    return Path(tempfile.gettempdir()).resolve()


@contextmanager
def signal_cleanup():
    """Convert non-ignored termination signals into SignalTerminated on the main thread."""
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

    signals = [signal.SIGINT, signal.SIGTERM]
    if hasattr(signal, "SIGHUP"):
        signals.append(signal.SIGHUP)
    for signum in signals:
        current = signal.getsignal(signum)
        if current is signal.SIG_IGN:
            continue
        previous[signum] = current
        signal.signal(signum, handle)
    try:
        yield
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def _listing(columns):
    """Return each process's fields for the ps columns, in one snapshot, or None when ps fails."""
    try:
        done = subprocess.run(["ps", "-A", "-o", columns], capture_output=True, text=True, check=False)
    except OSError:
        return None
    if done.returncode:
        return None
    return [line.split() for line in done.stdout.splitlines()]


def _descendants(pid):
    """Return the pids of every process below pid in one ps snapshot, or None when ps fails."""
    listing = _listing("pid=,ppid=")
    if listing is None:
        return None
    children = {}
    for fields in listing:
        if len(fields) == 2 and fields[0].isdigit() and fields[1].isdigit():
            children.setdefault(int(fields[1]), []).append(int(fields[0]))
    found, pending = [], [pid]
    while pending:
        below = children.get(pending.pop(), [])
        found += below
        pending += below
    return found


def stop_process(process):
    """Terminate a spawned subprocess and the processes it started, keeping them in the caller's process group."""
    if process.poll() is not None:
        return
    # Freeze the tree before signalling it: a stopped process cannot start another or leave its children orphaned.
    frozen = [process.pid]
    try:
        with suppress(ProcessLookupError):
            process.send_signal(signal.SIGSTOP)
        if process.returncode is not None:
            return
        while True:
            listed = _descendants(process.pid)
            if listed is None:
                sys.stderr.write("WARN ps cannot list the processes that the checker started; they may still be running\n")
                break
            new = [pid for pid in listed if pid not in frozen]
            if not new:
                break
            frozen += new
            for pid in new:
                with suppress(OSError):
                    os.kill(pid, signal.SIGSTOP)
    finally:
        # send_signal reaps a checker that exited since poll and signals nothing; its pid is then free for reuse.
        if process.returncode is not None:
            frozen.remove(process.pid)
        for signum in (signal.SIGTERM, signal.SIGCONT):
            for pid in frozen:
                with suppress(OSError):
                    os.kill(pid, signum)
    deadline = time.monotonic() + 2
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        try:
            process.kill()
        except ProcessLookupError:
            pass
        process.wait()
    # A descendant that ignores SIGTERM, as one that inherits an ignored SIGTERM does, gets SIGKILL as the checker does.
    survivors = [pid for pid in frozen if pid != process.pid]
    while survivors:
        survivors = _running(survivors)
        if not survivors or time.monotonic() >= deadline:
            break
        time.sleep(0.05)
    for pid in survivors:
        with suppress(OSError):
            os.kill(pid, signal.SIGKILL)


def _running(pids):
    """Return the pids that still run. A zombie has exited, though a parent that never reaps keeps its pid."""
    listing = _listing("pid=,stat=")
    if listing is None:
        return [pid for pid in pids if _exists(pid)]
    running = {int(fields[0]) for fields in listing
               if len(fields) == 2 and fields[0].isdigit() and not fields[1].startswith("Z")}
    return [pid for pid in pids if pid in running]


def _exists(pid):
    try:
        os.kill(pid, 0)
    except OSError:
        return False
    return True


def run_captured(command, **kwargs):
    """Run a command in the caller's process group and terminate it cleanly on interruption."""
    process = subprocess.Popen(
        command,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        **kwargs,
    )
    try:
        stdout, stderr = process.communicate()
    except BaseException:
        stop_process(process)
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
    return any(mount == prefix or mount.startswith(prefix + "/") for prefix in SKIP_MOUNT_PREFIXES)


def parse_df_mounts(
    df_text,
    temp_root,
    root_path=Path("/"),
    *,
    stat_fn=os.stat,
    access_fn=os.access,
    usage_fn=shutil.disk_usage,
):
    """Return writable local mounted volume directories with more free space than temp_root."""
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
            st = stat_fn(mount)
            if not stat.S_ISDIR(st.st_mode):
                continue
            dev = st.st_dev
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


def _suggested_tmpdir(mount):
    return shlex.quote(str(Path(mount) / ".tmp" / "formal-verify"))


def format_report(report):
    """Format preflight storage lines for setup.sh and interactive agent checks."""
    lines = [f"TEMP_DIR {report.temp_root} ({report.temp_free / GIB:.1f} GiB free)"]
    if not report.same_device:
        lines.append(f"SYSTEM_DISK / ({report.root_free / GIB:.1f} GiB free)")
    threshold = report.min_gib * GIB
    # Warn on / only when TMPDIR still shares the root device; once TMPDIR moves off /,
    # a low root volume should not repeat an unclearable warning.
    low_temp = report.min_gib > 0 and report.temp_free < threshold
    low_root = report.same_device and report.min_gib > 0 and report.root_free < threshold
    if low_temp or low_root:
        lines.append(
            f"WARN low free space (< {report.min_gib} GiB): temp dir {report.temp_root} has "
            f"{report.temp_free / GIB:.1f} GiB free, system disk / has {report.root_free / GIB:.1f} GiB free; "
            "TLC disk queues or Kani build dirs may exhaust disk space. Set TMPDIR=<dir> to choose another volume."
        )
    for mount, free in report.candidates:
        lines.append(f"EXTERNAL_VOLUME {mount} ({free / GIB:.1f} GiB free; suggested TMPDIR={_suggested_tmpdir(mount)})")
    return lines


def warn_runtime():
    """Emit a single per-process stderr warning if active temporary space is critically low."""
    global _warned_runtime
    if _warned_runtime:
        return
    _warned_runtime = True
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
        sys.stderr.write(f"WARN candidate volume {mount} ({free / GIB:.1f} GiB free; suggested TMPDIR={_suggested_tmpdir(mount)})\n")
    sys.stderr.flush()


def main():
    action = sys.argv[1] if len(sys.argv) == 2 else ""
    try:
        if action == "report":
            for line in format_report(inspect_storage()):
                print(line)
            return 0
        if action == "warn":
            warn_runtime()
            return 0
    except TempDirError as error:
        print(error)
        return 1
    print("usage: workdir.py <report|warn>", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
