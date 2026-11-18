#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Model-check TLA+ specs with TLC over a matrix of constants read from a matrix file.

Prints one PASS or FAIL line per run with its distinct state count, then a
SUMMARY line with the totals. A failing run prints TLC's error and its error
trace reduced to the variables each step changed (tlc-trace.py).

Matrix file, one directive per line (# starts a comment):
  spec <path.tla>             the spec for the runs below, relative to the file;
                              TLC checks the formula it names Spec
  check <cfg line>            an INVARIANTS or PROPERTIES line, kept until the next spec
  reach <Operator> | <label-substring>   a witness in the first matching run
  run <label> | <Name=Value ...>   one TLC run with those CONSTANTS

A malformed directive prints a FAIL line and the runner goes on to the next.

Usage: tlc-matrix.sh <matrix-file> [label-substring]
  TLC_JAR=<path>     use this existing tla2tools.jar
  TLC_CACHE=<dir>    where the pinned jar lives (default ~/.cache/tla)
  JAVA=<path>        the java binary (default: java on PATH)
  TLC_WORKERS=<n>    TLC worker threads (default auto)
  TLC_TIMEOUT=<lim>  per-run time limit, e.g. 90s, 30m, 1h (default 30m)
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
import time
import uuid
from dataclasses import dataclass, replace
from enum import Enum
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_KINDS = ("INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES")
REACH = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*)\s*\|\s*(.*\S)\s*")


def read_raw(path):
    """Return a file's text as bash reads it: line ends untouched, a byte that is not UTF-8 replaced."""
    with open(path, encoding="utf-8", errors="replace", newline="") as stream:
        return stream.read()


@dataclass(frozen=True)
class Spec:
    path: str


@dataclass(frozen=True)
class Check:
    line: str
    kind: str
    names: tuple


@dataclass(frozen=True)
class Reach:
    operator: str
    match: str


@dataclass(frozen=True)
class Run:
    label: str
    constants: str


@dataclass(frozen=True)
class Malformed:
    message: str


def _directives(lines):
    """Yield each directive of a matrix in file order, with a Malformed in place of a line it rejects."""
    seen_spec = False
    for raw in lines:
        line = raw.split("#", 1)[0]
        if not line.strip():
            continue
        keyword, rest = (line.split(None, 1) + [""])[:2]
        rest = rest.strip()
        if keyword == "spec":
            seen_spec = bool(rest)
            yield Spec(rest)
        elif keyword == "check":
            kind, names = (rest.split(None, 1) + ["", ""])[:2]
            if not seen_spec:
                yield Malformed(f"check '{rest}' before any spec line")
            elif kind not in CHECK_KINDS or not names.strip():
                yield Malformed(f"malformed check '{rest}'")
            else:
                yield Check(rest, kind, tuple(names.split()))
        elif keyword == "reach":
            match = REACH.fullmatch(rest)
            if not seen_spec:
                yield Malformed(f"reach '{rest}' before any spec line")
            elif not match:
                yield Malformed(f"malformed reach '{rest}': expected reach <Operator> | <label-substring>")
            else:
                yield Reach(match[1], match[2])
        elif keyword == "run":
            label, bar, constants = rest.partition("|")
            if not bar:
                yield Malformed(f"run '{rest}' has no | before its constants")
            elif not seen_spec:
                yield Malformed(f"run '{label.rstrip()}' before any spec line")
            else:
                yield Run(label.rstrip(), constants)
        else:
            yield Malformed(f"unknown directive: {line}")


class Unavailable(Exception):
    pass


DEFAULT_TIMEOUT = "30m"
TIME_UNITS = {"": 1, "s": 1, "m": 60, "h": 3600}
PROGRESS_DELAY = 15.0
PROGRESS_INTERVAL = 30.0


def parse_timeout(raw):
    """Parse a positive integer duration with optional s/m/h unit into (normalized_label, seconds)."""
    limit = re.fullmatch(r"\+?0*([1-9][0-9]{0,9})([smh]?)", raw)
    if not limit or int(limit[1]) >= 2**32:
        raise Unavailable(
            f"UNAVAILABLE TLC_TIMEOUT={raw!r} is not a run time limit; set a whole number from 1 to 4294967295 "
            "with an optional unit s, m or h, such as 90s or 20m, or unset it for thirty minutes"
        )
    unit = limit[2] or "s"
    return limit[1] + unit, int(limit[1]) * TIME_UNITS[limit[2]]


def _stop_process(process):
    """Terminate a spawned TLC process cleanly while keeping it in the caller's process group."""
    if process.poll() is not None:
        return
    try:
        process.terminate()
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        try:
            process.kill()
        except ProcessLookupError:
            pass
        process.wait()


def _read_progress(log_path, offset, partial):
    """Read newly written complete lines from tlc.log and return (new_offset, new_partial, latest_progress)."""
    latest = ""
    try:
        with log_path.open("r", encoding="utf-8", errors="replace") as stream:
            stream.seek(offset)
            chunk = stream.read()
            new_offset = stream.tell()
    except OSError:
        return offset, partial, ""
    if not chunk:
        return new_offset, partial, ""
    text = partial + chunk
    lines = text.splitlines(keepends=True)
    if lines and not lines[-1].endswith(("\n", "\r")):
        new_partial = lines.pop()
    else:
        new_partial = ""
    for line in lines:
        stripped = line.strip()
        if "Progress(" in stripped:
            latest = stripped
    return new_offset, new_partial, latest


class Tlc:
    """The pinned TLC, checked once; tlc-tools.sh owns the pin and the readiness checks."""

    def __init__(self):
        timeout_raw = os.environ.get("TLC_TIMEOUT", "").strip() or DEFAULT_TIMEOUT
        self.limit, self.timeout_seconds = parse_timeout(timeout_raw)
        done = subprocess.run(
            ["bash", "-c", 'source "$1/tlc-tools.sh" && require_tlc_runtime && tlc_jar_ready && printf "%s\\n%s\\n" "$JAVA" "$TLC_JAR"',
             "bash", str(HERE)], capture_output=True, text=True, check=False)
        if done.returncode:
            raise Unavailable(done.stdout.rstrip("\n"))
        self.java, self.jar = done.stdout.splitlines()[-2:]
        self.workers = os.environ.get("TLC_WORKERS") or "auto"

    def run(self, directory, module, config, reach, workers=None, progress_label=""):
        """Run TLC on module in directory with config; return (exit_status, log, timed_out)."""
        log = directory / "tlc.log"
        (directory / "MC.cfg").write_text(config, encoding="utf-8")
        chosen_workers = workers if workers is not None else ("1" if reach else self.workers)
        command = [self.java, "-XX:+UseParallelGC", "-cp", self.jar, "tlc2.TLC", "-workers", chosen_workers,
                   *(["-deadlock"] if reach else []), "-cleanup", "-metadir", str(directory / "states"),
                   "-config", str(directory / "MC.cfg"), str(directory / f"{module}.tla")]
        start = time.monotonic()
        deadline = start + self.timeout_seconds
        next_report = start + PROGRESS_DELAY
        offset, partial, latest = 0, "", ""
        timed_out = False
        with log.open("w", encoding="utf-8") as stream:
            process = subprocess.Popen(command, stdout=stream, stderr=subprocess.STDOUT)
            try:
                while True:
                    now = time.monotonic()
                    remaining = deadline - now
                    if remaining <= 0:
                        _stop_process(process)
                        timed_out = True
                        break
                    if now >= next_report:
                        offset, partial, found = _read_progress(log, offset, partial)
                        if found:
                            latest = found
                        elapsed = int(now - start)
                        prefix = f"[tlc] {progress_label}: " if progress_label else "[tlc] "
                        body = f"{elapsed}s elapsed: {latest}" if latest else f"{elapsed}s elapsed"
                        sys.stderr.write(f"{prefix}{body}\n")
                        sys.stderr.flush()
                        next_report = now + PROGRESS_INTERVAL
                    wait_for = min(remaining, max(0.05, next_report - time.monotonic()))
                    try:
                        process.wait(timeout=wait_for)
                        break
                    except subprocess.TimeoutExpired:
                        continue
            finally:
                if process.poll() is None:
                    _stop_process(process)
            status = process.returncode
        return status, read_raw(log), timed_out


class Outcome(Enum):
    PASS = "pass"
    FAIL = "fail"
    MISSING = "missing"
    WITNESS = "witness"
    UNREACHED = "unreached"
    INCOMPLETE = "incomplete"
    NO_RUN = "no run"
    MALFORMED = "malformed"


@dataclass(frozen=True)
class Result:
    """One line of the runner's report and the output printed under it."""
    outcome: Outcome
    name: str = ""
    label: str = ""
    operator: str = ""
    detail: str = ""
    lines: tuple = ()


@dataclass(frozen=True)
class Task:
    spec: str
    run: Run
    checks: tuple = ()
    reach: Reach | None = None
    check_deadlock: bool = True


class _Section:
    """A spec occurrence owns its declared checks and the runs to which each applies."""

    def __init__(self, spec, directives):
        self.spec = spec
        self.properties = set()
        self.reaches = set()
        self.tasks = []
        checks, reaches, runs = [], [], []
        for directive in directives:
            if isinstance(directive, Check):
                checks.append(directive)
                self.properties.update(directive.names)
            elif isinstance(directive, Reach):
                reaches.append(directive)
                self.reaches.add(f"reach:{directive.operator}")
            elif isinstance(directive, Run):
                runs.append(directive)
                self.tasks.append(Task(spec, directive, tuple(checks)))
            else:
                self.tasks.append(Result(Outcome.MALFORMED, detail=directive.message))
        for reach in reaches:
            run = next((run for run in runs if reach.match in run.label), None)
            if run is None:
                self.tasks.append(Result(Outcome.NO_RUN, Path(spec).name.removesuffix(".tla"), operator=reach.operator, detail=reach.match))
            else:
                self.tasks.append(Task(spec, run, reach=reach))


class MatrixPlan:
    """Compile a matrix once for execution, specification recording or mutation selection."""

    def __init__(self, path):
        self.path = Path(path)
        self._sections = []
        spec, body = None, []
        for directive in _directives(read_raw(self.path).split("\n")):
            if isinstance(directive, Spec):
                self._sections.append(_Section(spec, body))
                spec, body = directive.path, []
            else:
                body.append(directive)
        self._sections.append(_Section(spec, body))

    def __iter__(self):
        for section in self._sections:
            yield from section.tasks

    @property
    def specs(self):
        return [section.spec for section in self._sections if section.spec is not None]

    def checked_tasks(self):
        """A baseline needs every task to be resolved, including every reach."""
        errors = ["; ".join(render(task)) for task in self if isinstance(task, Result)]
        if errors:
            raise ValueError(f"{self.path}: {'; '.join(errors)}")
        if "" in self.specs:
            raise ValueError(f"{self.path}: spec line has no path")
        return iter(self)

    def mutations_for(self, spec):
        spec = Path(spec).resolve()
        for task in self:
            if isinstance(task, Result) and task.outcome is Outcome.MALFORMED:
                raise ValueError(f"{self.path}: {task.detail}")
        sections = [section for section in self._sections
                    if section.spec and (self.path.parent / section.spec).resolve() == spec]
        return MutationPlan(spec, sections)


class MutationPlan:
    """Run a named detector on exactly the tasks selected for a copied spec."""

    def __init__(self, spec, sections):
        self._spec = spec
        self._passing_originals = set()
        self.properties = {name for section in sections for name in section.properties}
        self.detectors = self.properties | {name for section in sections for name in section.reaches}
        self._tasks = [task for section in sections for task in section.tasks]

    def _select(self, detector):
        for task in self._tasks:
            if isinstance(task, Result):
                if f"reach:{task.operator}" == detector:
                    yield task
            elif task.reach:
                if f"reach:{task.reach.operator}" == detector:
                    yield replace(task, spec=self._spec.name)
            else:
                checks = tuple(Check(f"{check.kind} {detector}", check.kind, (detector,))
                               for check in task.checks if detector in check.names)
                if checks:
                    yield Task(self._spec.name, task.run, checks,
                               check_deadlock=not any(check.kind.startswith("PROPERT") for check in checks))

    def check(self, checker, detector, only, source, work):
        """Return the first confirmed detection, None for a miss, or raise on inconclusive evidence."""
        results = []
        for task in self._select(detector):
            if isinstance(task, Result):
                results.append(task)
                continue
            if only not in task.run.label:
                continue
            if task not in self._passing_originals:
                original = run_task(checker, self._spec.parent, task, work)
                if original.outcome not in (Outcome.PASS, Outcome.WITNESS):
                    raise ValueError(f"unmutated model did not pass {detector}: " + "\n".join(render(original)))
                self._passing_originals.add(task)
            results.append(run_task(checker, self._spec.parent, task, work, source))
        if not results:
            raise ValueError(f"no run matches '{only}' for '{detector}'")
        violations = {
            f"Error: Invariant {detector} is violated.",
            f"Error: Invariant {detector} is violated by the initial state:",
            f"Error: Property {detector} is violated by the initial state:",
            f"Error: Action property {detector} is violated.",
            "Error: Temporal properties were violated.",
        }
        detections, errors = [], []
        for result in results:
            if result.outcome is Outcome.UNREACHED:
                detections.append((result.label, "the model never reaches this state"))
            elif result.outcome is Outcome.FAIL and result.detail in violations:
                detections.append((result.label, result.detail.removeprefix("Error: ").rstrip(".")))
            elif result.outcome not in (Outcome.PASS, Outcome.WITNESS):
                errors.extend(render(result))
        if errors:
            raise ValueError("\n".join(errors))
        if detections:
            label, reason = detections[0]
            return f"{detector} fails in run '{label}' ({reason})"
        return None


def render(result):
    """Return the lines the matrix runner prints for one result."""
    name, label, operator = result.name, result.label, result.operator
    head = {
        Outcome.PASS: f"PASS {name} {label} {result.detail}",
        Outcome.FAIL: f"FAIL {name} {label}: {result.detail}",
        Outcome.MISSING: f"FAIL {name} {label}: spec {result.detail} not found",
        Outcome.WITNESS: f"PASS {name} reach {operator} {label}: shortest trace {result.detail}",
        Outcome.UNREACHED: f"FAIL {name} reach {operator} {label}: the model never reaches this state",
        Outcome.INCOMPLETE: f"FAIL {name} reach {operator} {label}: TLC did not complete the reach check",
        Outcome.NO_RUN: f"FAIL {name} reach {operator}: no run matching '{result.detail}'",
        Outcome.MALFORMED: f"FAIL {result.detail}",
    }[result.outcome]
    return [head, *result.lines]


def reduced_trace(log_path, log):
    done = subprocess.run([sys.executable, str(HERE / "tlc-trace.py"), str(log_path)], capture_output=True, text=True, check=False)
    sys.stderr.write(done.stderr)
    lines = done.stdout.removesuffix("\n").split("\n") if done.stdout else []
    if done.returncode:
        lines += [line for line in log.split("\n") if line.strip()][-40:]
    return lines


def run_task(checker, matrix_dir, task, work, source=None):
    """Execute a resolved matrix task, optionally replacing its spec in the private run directory."""
    spec, run = task.spec, task.run
    operator = task.reach.operator if task.reach else ""
    name = Path(spec).name.removesuffix(".tla")
    if not (matrix_dir / spec).is_file():
        return Result(Outcome.MISSING, name, run.label, detail=spec)
    directory = Path(tempfile.mkdtemp(prefix="run.", dir=work))
    for module in (matrix_dir / spec).parent.glob("*.tla"):
        dest = directory / module.name
        if source is not None and module.name == Path(spec).name:
            dest.write_text(source, encoding="utf-8")
        else:
            dest.write_bytes(module.read_bytes())
    constants = "".join(f"  {pair.split('=')[0]} = {pair.split('=', 1)[-1]}\n" for pair in run.constants.split())
    config = f"CONSTANTS\n{constants}SPECIFICATION Spec\n"
    if not task.check_deadlock:
        config += "CHECK_DEADLOCK FALSE\n"
    if not operator:
        status, log, timed_out = checker.run(
            directory, name, config + "\n".join(check.line for check in task.checks) + "\n",
            reach=False, progress_label=f"{name} {run.label}",
        )
        return ordinary(name, run, status, log, directory / "tlc.log", checker.limit if timed_out else None)
    wrapper = f"Reach{uuid.uuid4().hex}"
    invariant = f"{wrapper}Negated"
    (directory / f"{wrapper}.tla").write_text(f"---- MODULE {wrapper} ----\nEXTENDS {name}\n{invariant} == ~{operator}\n====\n", encoding="utf-8")
    # Exhaustive UNREACHED checks in reach: mutations do not depend on shortest-trace determinism.
    reach_workers = checker.workers if source is not None else "1"
    status, log, timed_out = checker.run(
        directory, wrapper, config + f"INVARIANT {invariant}\n",
        reach=True, workers=reach_workers, progress_label=f"{name} reach {operator} {run.label}",
    )
    return witness(name, run, operator, invariant, status, log, checker.limit if timed_out else None)



def ordinary(name, run, status, log, log_path, timeout_limit=None):
    if timeout_limit:
        tail = tuple(line for line in log.split("\n") if line.strip())[-10:]
        return Result(Outcome.FAIL, name, run.label,
                      detail=f"TLC timed out after {timeout_limit}; set TLC_TIMEOUT to change the limit", lines=tail)
    if status == 0 and "No error has been found" in log:
        found = re.findall(r"[0-9,]* distinct states found", log)
        states = found[-1] if found else ""
        return Result(Outcome.PASS, name, run.label, detail=states)
    errors = [line for line in log.split("\n") if line.startswith("Error:")]
    return Result(Outcome.FAIL, name, run.label, detail=errors[0] if errors else "",
                  lines=(*errors[1:5], *reduced_trace(log_path, log)))


def witness(name, run, operator, invariant, status, log, timeout_limit=None):
    if timeout_limit:
        tail = tuple(line for line in log.split("\n") if line.strip())[-10:]
        return Result(Outcome.INCOMPLETE, name, run.label, operator,
                      lines=(f"TLC timed out after {timeout_limit}; set TLC_TIMEOUT to change the limit", *tail))
    lines = log.split("\n")
    length = 0
    if status == 12 and f"Error: Invariant {invariant} is violated by the initial state:" in lines:
        length = 1
    elif status == 12 and f"Error: Invariant {invariant} is violated." in lines:
        length = sum(1 for line in lines if re.match(r"State [0-9]+:", line))
    if length:
        return Result(Outcome.WITNESS, name, run.label, operator, f"{length} states ({length - 1} transitions)")
    if status == 0 and "No error has been found" in log:
        return Result(Outcome.UNREACHED, name, run.label, operator)
    return Result(Outcome.INCOMPLETE, name, run.label, operator, lines=tuple(log.removesuffix("\n").split("\n")) if log else ())


class Runner:
    """Run the selected tasks and report each result to emit."""

    def __init__(self, tlc, matrix_dir, only, emit, work):
        self.tlc, self.matrix_dir, self.only, self.emit, self.work = tlc, matrix_dir, only, emit, work
        self.runs_total = self.passed = self.states = self.reach_total = self.reached = 0
        self.failed = False

    def report(self, result):
        self.failed |= result.outcome not in (Outcome.PASS, Outcome.WITNESS)
        self.emit(result)

    def check(self, task):
        if isinstance(task, Result):
            self.reach_total += task.outcome is Outcome.NO_RUN
            self.report(task)
            return
        if self.only not in task.run.label:
            return
        if task.reach:
            self.reach_total += 1
        else:
            self.runs_total += 1
        result = run_task(self.tlc, self.matrix_dir, task, self.work)
        if result.outcome is Outcome.PASS:
            self.passed += 1
            self.states += int(result.detail.partition(" ")[0].replace(",", "") or 0)
        elif result.outcome is Outcome.WITNESS:
            self.reached += 1
        self.report(result)


def main():
    if not 2 <= len(sys.argv) <= 3:
        print("usage: tlc-matrix.sh <matrix-file> [label-substring]")
        return 2
    matrix, only = sys.argv[1], sys.argv[2] if len(sys.argv) == 3 else ""
    if not Path(matrix).is_file():
        print(f"FAIL {matrix} does not exist")
        return 1
    try:
        tlc = Tlc()
    except Unavailable as error:
        print(error)
        return 3
    with tempfile.TemporaryDirectory() as work:
        runner = Runner(tlc, Path(matrix).resolve().parent, only, lambda result: print("\n".join(render(result)), flush=True), Path(work))
        for task in MatrixPlan(matrix):
            runner.check(task)
    if runner.runs_total == 0:
        matching = f"matching '{only}' " if only else ""
        print(f"FAIL no run {matching}in {matrix}")
        return 1
    summary = f"SUMMARY {runner.passed} of {runner.runs_total} runs passed"
    if runner.reach_total:
        summary += f", {runner.reached} of {runner.reach_total} reach checks passed"
    print(f"{summary}, {runner.states} distinct states in total")
    return int(runner.failed)


if __name__ == "__main__":
    sys.exit(main())
