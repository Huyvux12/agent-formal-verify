#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Run checkers so that a signal or an error stops each one and every process it started.

Usage: processes.py run <command> [<argument> ...]
  Run a command on this process's streams; a shell script runs a long step through here so that its
  signal trap can stop the step's whole process tree. Exits with the command's status as a shell reports it.
"""
import os
import signal
import subprocess
import sys
import threading
import time
from contextlib import contextmanager, suppress

# While guarded starts a process, the signals that signal_cleanup catches wait here until the process can be stopped.
_deferred = None
# Bounds on one stop: how long its ps listings of the checker's descendants may take together,
# and how many it takes before signalling what it found, in case a process keeps starting others.
PS_TIMEOUT = 5
MAX_LISTINGS = 50
# The termination signals that signal_cleanup converts and that a stop holds back until it finishes.
HANDLED = (signal.SIGINT, signal.SIGTERM, *((signal.SIGHUP,) if hasattr(signal, "SIGHUP") else ()))


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
        if _deferred is not None:
            _deferred.append(signum)
            return
        raise SignalTerminated(signum)

    for signum in HANDLED:
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


def _listing(columns, timeout):
    """Return each process's fields for the ps columns, in one snapshot, or None when ps fails or takes too long."""
    try:
        process = subprocess.Popen(["ps", "-A", "-o", columns], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                   text=True)
    except OSError:
        return None
    try:
        stdout = process.communicate(timeout=timeout)[0]
    except subprocess.TimeoutExpired:
        stdout = None
    finally:
        if process.returncode is None:
            process.kill()
            # A ps in uninterruptible sleep cannot die until its read returns, so it is left behind, not waited for.
            with suppress(subprocess.TimeoutExpired):
                process.wait(timeout=1)
    if stdout is None or process.returncode:
        return None
    return [line.split() for line in stdout.splitlines()]


def _descendants(pid, timeout):
    """Return the pids of every process below pid in one ps snapshot, or None when ps fails or takes too long."""
    listing = _listing("pid=,ppid=", timeout)
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
    """Terminate a spawned subprocess and the processes it started, keeping them in the caller's process group.

    The termination signals that signal_cleanup handles are blocked for the whole stop, so a signal that arrives
    meanwhile is raised once every process is gone and no step of the stop is cut short.
    """
    if process.poll() is not None:
        return
    # Save the mask before blocking: a handler that runs inside the blocking call can raise, and must leave it restored.
    blocked = signal.pthread_sigmask(signal.SIG_BLOCK, ())
    try:
        signal.pthread_sigmask(signal.SIG_BLOCK, HANDLED)
        _stop(process)
    finally:
        signal.pthread_sigmask(signal.SIG_SETMASK, blocked)


def _stop(process):
    # Freeze the tree before signalling it: a stopped process cannot start another or leave its children orphaned.
    frozen = [process.pid]
    listing_deadline = time.monotonic() + PS_TIMEOUT
    try:
        with suppress(ProcessLookupError):
            process.send_signal(signal.SIGSTOP)
        if process.returncode is not None:
            return
        for _ in range(MAX_LISTINGS):
            listed = _descendants(process.pid, max(0, listing_deadline - time.monotonic()))
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
        else:
            sys.stderr.write(f"WARN the checker kept starting processes through {MAX_LISTINGS} ps listings; "
                             "processes it started later may still be running\n")
    finally:
        # An error in the listings, such as a warning that cannot be written, must not leave the frozen tree suspended.
        # send_signal reaps a checker that exited since poll and signals nothing; its pid is then free for reuse.
        if process.returncode is not None:
            frozen.remove(process.pid)
        for signum in (signal.SIGTERM, signal.SIGCONT):
            for pid in frozen:
                with suppress(OSError):
                    os.kill(pid, signum)
    survivors = [pid for pid in frozen if pid != process.pid]
    deadline = time.monotonic() + 2
    with suppress(subprocess.TimeoutExpired):
        process.wait(timeout=2)
    while survivors and time.monotonic() < deadline:
        survivors = _running(survivors)
        if survivors:
            time.sleep(0.05)
    if process.returncode is None:
        with suppress(ProcessLookupError):
            process.kill()
        process.wait()
    # A descendant that ignores SIGTERM, as one that inherits an ignored SIGTERM does, gets SIGKILL as the checker does.
    if survivors:
        for pid in _running(survivors):
            with suppress(OSError):
                os.kill(pid, signal.SIGKILL)


def _running(pids):
    """Return the pids that still run. A zombie has exited, though a parent that never reaps keeps its pid."""
    listing = _listing("pid=,stat=", PS_TIMEOUT)
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


def guarded(command, body, **kwargs):
    """Start a command with Popen, return body(process), and stop the process if anything, a signal included, ends body early.

    A signal that arrives while Popen runs, which waits for the command to start, is raised only once the
    process exists. From then until body returns, every point where a signal handler can run is inside the
    try that stops the process, which a context manager's __enter__ could not guarantee.
    """
    global _deferred
    _deferred = deferred = []
    try:
        process = subprocess.Popen(command, **kwargs)
    except BaseException:
        _deferred = None
        if not deferred:
            raise
        raise SignalTerminated(deferred[0]) from None
    try:
        _deferred = None
        if deferred:
            raise SignalTerminated(deferred[0])
        return body(process)
    except BaseException:
        stop_process(process)
        raise


def run_captured(command, **kwargs):
    """Run a command in the caller's process group and terminate it cleanly on interruption."""
    def collect(process):
        stdout, stderr = process.communicate()
        return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
    return guarded(command, collect, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, **kwargs)


def run_inherited(command):
    """Run a command on this process's streams and return its exit status as a shell reports it."""
    started = []

    def wait(process):
        started.append(process)
        return process.wait()
    try:
        status = guarded(command, wait)
    except OSError as error:
        if started:
            raise
        print(f"cannot run {command[0]}: {error}", file=sys.stderr)
        return 127
    return 128 - status if status < 0 else status


def main():
    if len(sys.argv) < 3 or sys.argv[1] != "run":
        print("usage: processes.py run <command> [<argument> ...]", file=sys.stderr)
        return 2
    try:
        with signal_cleanup():
            return run_inherited(sys.argv[2:])
    except SignalTerminated as error:
        error.exit()


if __name__ == "__main__":
    sys.exit(main())
