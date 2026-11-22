# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Stop a checker as the TLC timeout path does, and deliver a real SIGINT to the runner while the stop runs.

Usage: python3 -B stop-under-signal.py <scripts-dir> <scenario> <scratch-dir>
Run it with <scratch-dir>/bin first on PATH, so the stop finds the fake ps that the listing scenarios write there.

The checker's child ignores SIGTERM, so only the stop's SIGKILL pass can end it. Scenarios:
  wait          the checker's SIGTERM trap signals the runner, which lands in the signal pass or the wait
  first-listing the first ps listing of the checker's descendants signals the runner
  kill-listing  the checker ignores SIGTERM too, and the ps listing before SIGKILL signals the runner

Prints how the guarded call ended, then the pids of the checker's child and of the checker, one per line.
"""
import subprocess
import sys
import time
from pathlib import Path

scripts, scenario, scratch = sys.argv[1], sys.argv[2], Path(sys.argv[3])
sys.path.insert(0, scripts)
import processes

child_pid = scratch / "child.pid"
checkers = {
    "wait": 'trap "kill -INT $PPID; exit 0" TERM; (trap "" TERM; exec sleep 30) & echo "$!" > "$1"; wait',
    "first-listing": '(trap "" TERM; exec sleep 30) & echo "$!" > "$1"; wait',
    "kill-listing": 'trap "" TERM; sleep 30 & echo "$!" > "$1"; wait',
}
# The stop lists descendants with the pid=,ppid= columns and running processes with pid=,stat=.
listings = {"first-listing": "*ppid=*", "kill-listing": "*stat=*"}
if scenario in listings:
    real_ps = subprocess.run(["sh", "-c", "command -v ps"], capture_output=True, text=True, check=True).stdout.strip()
    fake = scratch / "bin" / "ps"
    fake.parent.mkdir(exist_ok=True)
    fake.write_text(f'#!/bin/sh\ncase "$*" in {listings[scenario]})\n'
                    f'  [ -e "{scratch}/signalled" ] || {{ : > "{scratch}/signalled"; kill -INT "$PPID"; }} ;;\n'
                    f'esac\nexec "{real_ps}" "$@"\n')
    fake.chmod(0o755)


started = []


def body(process):
    started.append(process.pid)
    while not (child_pid.exists() and child_pid.read_text().endswith("\n")):
        time.sleep(0.02)
    processes.stop_process(process)
    return f"returned {process.returncode}"


with processes.signal_cleanup():
    try:
        outcome = processes.guarded(["bash", "-c", checkers[scenario], "checker", str(child_pid)], body,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except processes.SignalTerminated as error:
        outcome = f"SignalTerminated({error.signum})"
print(outcome)
print(child_pid.read_text().strip())
print(started[0])
