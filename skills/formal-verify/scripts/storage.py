#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Choose the temporary directory for checker runs and check its free space.

Usage: storage.py report | storage.py warn
  report  print the temporary directory, the system disk when it differs, a WARN line when either is low,
          and larger writable local volumes as EXTERNAL_VOLUME lines with a suggested TMPDIR
  warn    print one warning to stderr when the temporary directory is critically low
"""
from __future__ import annotations

import os
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
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


def report():
    """Print the preflight storage lines, as setup.sh reports them after each tool's readiness check."""
    for line in format_report(inspect_storage()):
        print(line)


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
            report()
            return 0
        if action == "warn":
            warn_runtime()
            return 0
    except TempDirError as error:
        print(error)
        return 1
    print("usage: storage.py report | storage.py warn", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
