# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Stop a checker while the stop's warning cannot be written, and report whether the checker was resumed.

Usage: python3 -B stop-after-error.py <scripts-dir>
Run it with a failing ps first on PATH, so the stop writes its warning to a stderr that is a closed pipe.
Prints how the stop ended, then the checker's exit status, or "suspended" if it never got SIGTERM and SIGCONT.
"""
import os
import subprocess
import sys

sys.path.insert(0, sys.argv[1])
import workdir

checker = subprocess.Popen(["sleep", "30"])
out = os.fdopen(os.dup(1), "w")
saved = os.dup(2)
reader, writer = os.pipe()
os.close(reader)
os.dup2(writer, 2)
try:
    workdir.stop_process(checker)
    ending = "returned"
except OSError as error:
    ending = f"raised {type(error).__name__}"
finally:
    os.dup2(saved, 2)
try:
    status = checker.wait(timeout=5)
except subprocess.TimeoutExpired:
    status = "suspended"
    checker.kill()
    checker.wait()
print(ending, file=out)
print(status, file=out, flush=True)
