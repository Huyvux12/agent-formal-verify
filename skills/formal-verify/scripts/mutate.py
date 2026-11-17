#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Check that a model's properties detect the bugs in its mutations file.

Takes <Name>.mutations, which sits beside <Name>.tla and <Name>.matrix or
beside <Name>.lean in a Lake project or <Name>.rs in a Rust crate. Applies each mutation to a temporary
copy, so the model in the repository is never changed, and prints one line
per mutation:

  DETECTED <label>: <what failed>   the mutated model fails as it should
  MISSED <label>                    the mutated model still passes
  UNCOVERED <Property>              a TLA+ property or Rust harness no mutation
                                    targets, or a Lean proof no mutation breaks

A TLA+ mutation is checked against the property or reach operator it names,
using the matrix runs. A Lean mutation is elaborated in the project, the mutated
module alone, and reported with the theorems, lemmas, examples and #guard
lines that fail. Every public theorem recorded in the model's .statements file
must have its proof fail on some mutation; a failing #guard does not cover it.
An error counts only for an original theorem, example or #guard with the same
elaborated statement. A new example cannot count by repeating an existing one's
statement. A changed statement gives the mutation no verdict.
Lean reports fully qualified theorem names from elaborated declarations.
This measures proof sensitivity, not whether a mutated statement is false or
its hypotheses can hold. Private theorems are proof helpers and need no mutation. Exits 1 on a MISSED or
UNCOVERED line, when a Lean model has no .statements file, or when a mutated
model fails for another reason, such as a syntax error, a definition that
no longer compiles or a Lean theorem, example or #guard whose statement the
mutation changes.

Mutations file (a line starting with # is a comment):
  mutation <label>          starts a mutation
  detects <Property>        TLA+ property or fully qualified Rust harness that must fail
  detects reach:<Operator>  TLA+ only: the reach check that must fail
  only <label-substring>    TLA+ only, optional: limits the matrix runs
  - <text>                  a line of the model to replace; the text of
                            consecutive lines must occur exactly once
  + <text>                  a line of the replacement; none deletes the text

A TLA+ or Rust mutation needs one detects line, and a Lean mutation takes
none. The runner reads every mutation and applies it to the model's text
before it runs any tool, so a malformed mutation stops the run first.

Usage: mutate.py <Name.mutations>
  The environment settings of tlc-matrix.sh apply to TLA+ mutations.
"""
import json
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass, replace
from enum import Enum
from functools import partial
from os.path import commonpath
from pathlib import Path

# Importing kani and tlc must not write __pycache__ into the skill directory.
sys.dont_write_bytecode = True

import kani
import tlc

HERE = Path(__file__).resolve().parent
LEAN_NOTE = "NOTE Lean detections mean existing proofs fail, not that theorem statements are false or hypotheses satisfiable."


DIRECTIVES = ("detects", "only", "-", "+")
SINGLE = ("detects", "only")


@dataclass(frozen=True)
class Language:
    name: str
    needs_detects: bool
    takes_only: bool
    runner: Callable


@dataclass(frozen=True)
class Mutation:
    label: str
    detects: str
    only: str
    old: str
    new: str
    original: str
    source: str


class Verdict(Enum):
    DETECTED = "DETECTED"
    MISSED = "MISSED"
    ERROR = "ERROR"


@dataclass(frozen=True)
class Result:
    verdict: Verdict
    detail: str = ""
    covers: frozenset = frozenset()


def stop(message, status=1):
    print(f"FAIL {message}")
    sys.exit(status)


def parse(path):
    """Return each mutation's label with its directives as (keyword, rest) pairs, in file order."""
    mutations = []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        keyword, _, rest = line.partition(" ")
        if keyword == "mutation":
            mutations.append((rest.strip(), []))
        elif not mutations:
            stop(f"{path}:{number}: '{line}' before any mutation line")
        elif keyword in DIRECTIVES:
            mutations[-1][1].append((keyword, rest))
        else:
            stop(f"{path}:{number}: unknown directive: {line}")
    if not mutations:
        stop(f"{path} has no mutation")
    return mutations


def make_mutation(label, directives, model, text, language):
    """Check one mutation's directives against its language and apply it to the model's text."""
    lines = {keyword: [rest for word, rest in directives if word == keyword] for keyword in DIRECTIVES}
    for keyword in SINGLE:
        if len(lines[keyword]) > 1:
            stop(f"mutation '{label}' has two {keyword} lines")
    if lines["detects"] and not language.needs_detects:
        stop(f"mutation '{label}': {language.name} mutations take no detects line; the runner names the theorems that fail")
    if language.needs_detects and not lines["detects"]:
        stop(f"mutation '{label}' has no detects line")
    if lines["only"] and not language.takes_only:
        stop(f"mutation '{label}': {language.name} mutations do not support 'only'")
    old = "\n".join(lines["-"])
    count = text.count(old) if old else 0
    if count != 1:
        stop(f"mutation '{label}': its - text occurs {count} times in {model}, want 1")
    detects, only = (lines[keyword][0].strip() if lines[keyword] else "" for keyword in SINGLE)
    new = "\n".join(lines["+"])
    return Mutation(label, detects, only, old, new, text, text.replace(old, new))


def check_tla(spec, checker, plan, mutation, work):
    """Narrow the matrix's existing tasks to the named mutation target without changing run scope."""
    for module in spec.parent.glob("*.tla"):
        (work / module.name).write_text(module.read_text(encoding="utf-8"), encoding="utf-8")
    (work / spec.name).write_text(mutation.source, encoding="utf-8")
    covers, results = frozenset({mutation.detects}), []
    runner = tlc.Runner(checker, work, mutation.only, results.append, work)
    for task in plan:
        if isinstance(task, tlc.Result):
            if f"reach:{task.operator}" == mutation.detects:
                runner.check(task)
        elif task.reach:
            if f"reach:{task.reach.operator}" == mutation.detects:
                runner.check(task)
        else:
            checks = tuple(tlc.Check(f"{check.kind} {mutation.detects}", check.kind, (mutation.detects,))
                           for check in task.checks if mutation.detects in check.names)
            if checks:
                runner.check(replace(task, checks=checks,
                                     check_deadlock=not any(check.kind.startswith("PROPERT") for check in checks)))
    if not results:
        return Result(Verdict.ERROR, f"no run matches '{mutation.only}' for '{mutation.detects}'")
    detected, errors = [], []
    for result in results:
        if result.outcome is tlc.Outcome.UNREACHED:
            detected.append((result, "the model never reaches this state"))
        elif result.outcome is tlc.Outcome.FAIL and (
                result.detail in (f"Error: Invariant {mutation.detects} is violated.",
                                  f"Error: Invariant {mutation.detects} is violated by the initial state:",
                                  f"Error: Property {mutation.detects} is violated by the initial state:",
                                  f"Error: Action property {mutation.detects} is violated.",
                                  "Error: Temporal properties were violated.")):
            detected.append((result, result.detail.removeprefix("Error: ").rstrip(".")))
        elif result.outcome not in (tlc.Outcome.PASS, tlc.Outcome.WITNESS):
            errors.extend(tlc.render(result))
    if errors:
        return Result(Verdict.ERROR, "\n".join(errors))
    if detected:
        result, error = detected[0]
        return Result(Verdict.DETECTED, f"{mutation.detects} fails in run '{result.label}' ({error})", covers)
    return Result(Verdict.MISSED, covers=covers)


def lean_toolchain(project):
    """Return the project's Lean pin once it is ready; lean-tools.sh owns the check and its remedy."""
    done = subprocess.run(["bash", "-c", 'source "$1/lean-tools.sh" && lean_ready_pin "$2"', "bash", str(HERE), str(project)],
                          capture_output=True, text=True, check=False)
    if done.returncode:
        print(done.stdout.strip())
        sys.exit(done.returncode)
    return done.stdout.strip()


def lean_analysis(model, project, toolchain):
    """Get Lean's declaration identities and error positions, never infer them from source text."""
    done = subprocess.run(["elan", "run", toolchain, "lake", "--dir", str(project), "env", "lean", "--run",
                           str(HERE / "lean-mutations.lean"), str(model)], capture_output=True, text=True, check=False)
    output = done.stdout + done.stderr
    records = [line.removeprefix("AFV_LEAN ") for line in done.stdout.splitlines() if line.startswith("AFV_LEAN ")]
    if done.returncode != 0 or len(records) != 1:
        stop(f"Lean declaration analysis did not complete:\n{output.strip()}")
    try:
        analysis = json.loads(records[0])
        for field in ("declarations", "commands", "errors"):
            if not isinstance(analysis[field], list):
                raise TypeError(f"{field} must be a list")
    except (ValueError, KeyError, TypeError) as error:
        stop(f"invalid Lean declaration analysis: {error}")
    return analysis


def contains(item, position):
    return item["start"] <= position < item["end"]


def command_sites(source, commands, edit_start, edit_end):
    """Identify anonymous checks by the source that survives the edit on either side."""
    line_starts = [0]
    for line in source.split("\n"):
        line_starts.append(line_starts[-1] + len(line) + 1)
    for cmd in commands:
        if not cmd["property"]:
            continue
        first, last = (line_starts[line - 1] + column for line, column in (cmd["start"], cmd["end"]))
        if last <= edit_start:
            site = ("before", first)
        elif first >= edit_end:
            site = ("after", first - edit_end)
        else:
            # An edit can split a check in two. Either surviving endpoint alone could name the new check.
            site = ("restated", source[first:last])
        yield (cmd["property"], site), cmd, first


def compare_commands(model, before, mutation, after):
    start = mutation.original.index(mutation.old)
    end = start + len(mutation.new)
    originals = {}
    for site, cmd, _ in command_sites(mutation.original, before, start, start + len(mutation.old)):
        originals.setdefault(site, []).append(cmd["statement"])
    commands = list(command_sites(mutation.source, after, start, end))
    counts = Counter(site for site, _, _ in commands)
    line_shift = mutation.old.count("\n") - mutation.new.count("\n")
    edit_line = mutation.original.count("\n", 0, start) + 1
    for site, cmd, offset in commands:
        candidates = originals.get(site, [])
        if len(candidates) != 1 or counts[site] != 1:
            reason = f"cannot match this {cmd['property']} to a single original check"
        elif cmd["statement"] is None or candidates[0] != cmd["statement"]:
            reason = "the mutation changes its statement"
        else:
            reason = ""
        line = cmd["start"][0]
        if start <= offset < end:
            location = f"{edit_line} (mutation replacement)"
        else:
            location = str(line + line_shift if offset >= end else line)
        yield cmd, f"{cmd['property']} at {model}:{location}", reason


def is_witness(name, declarations):
    parent, _, last = name.rpartition(".")
    return last == "witness" and any(decl["theorem"] and decl["name"] == parent for decl in declarations)


def check_lean(model, project, toolchain, theorems, commands, mutation, work):
    """Credit errors only to an original theorem or check with the same elaborated statement."""
    copy = work / model.name
    copy.write_text(mutation.source, encoding="utf-8")
    analysis = lean_analysis(copy, project, toolchain)
    if not analysis["errors"]:
        return Result(Verdict.MISSED)
    compared = list(compare_commands(model, commands, mutation, analysis["commands"]))
    failed = []
    for error in analysis["errors"]:
        position = [error["pos"]["line"], error["pos"]["column"]]
        where = f"{error['fileName']}:{position[0]}:{position[1]}: {error['data']}"
        checks = [("theorem " + decl["name"], decl["name"],
                   "" if (decl["name"], decl["type"]) in theorems else "the mutation changes its statement")
                  for decl in analysis["declarations"] if decl["theorem"] and contains(decl, position)]
        if not checks:
            checks = [(name, cmd["property"], reason) for cmd, name, reason in compared if contains(cmd, position)]
        for name, _, reason in checks:
            if reason:
                return Result(Verdict.ERROR, f"{name}: {reason}, so this error does not show its proof or check failing\n{where}")
        if error["fileName"] != str(copy) or not checks:
            return Result(Verdict.ERROR, where)
        failed.extend(name for name, property, _ in checks
                      if name not in failed and not is_witness(property, analysis["declarations"]))
    if not failed:
        return Result(Verdict.MISSED)
    return Result(Verdict.DETECTED, "proof/check fails: " + "; ".join(failed), frozenset(failed))


def check_rust(model, project, verifier, bounds, sources, mutation, work):
    """Run Kani on the named harness in a mutated copy of the crate; the mutation covers that harness."""
    anchor = Path(commonpath(sources))
    for source in sources:
        if not any(parent in sources for parent in source.parents):
            shutil.copytree(source, work / "source" / source.relative_to(anchor), ignore=shutil.ignore_patterns("target", ".git"))
    copy, covers = work / "source" / project.relative_to(anchor), frozenset({mutation.detects})
    (copy / model.relative_to(project)).write_text(mutation.source, encoding="utf-8")
    # Cargo resolves configuration from cwd, including paths outside the copied packages.
    outcome = kani.verify(copy, work, verifier, mutation.detects, bounds[mutation.detects].unwind, cwd=project)
    if outcome.verdict is kani.Verdict.PASS:
        return Result(Verdict.MISSED, covers=covers)
    if outcome.verdict is kani.Verdict.REFUTED:
        return Result(Verdict.DETECTED, "; ".join(outcome.failures), covers)
    return Result(Verdict.ERROR, "\n".join(outcome.failures) + "\n" + outcome.output)


def project_root(model, *markers):
    return next((parent for parent in model.parents if any((parent / marker).is_file() for marker in markers)), None)


def tla_runner(spec, mutations):
    """Preserve the execution plan of every matching spec section, and check TLC once."""
    matrix = spec.with_suffix(".matrix")
    if not matrix.is_file():
        stop(f"{matrix} is missing; mutations use its checks and runs")
    section, ours = [], False
    for directive in tlc.directives(tlc.read_raw(matrix).split("\n")):
        if isinstance(directive, tlc.Malformed):
            stop(f"{matrix}: {directive.message}")
        if isinstance(directive, tlc.Spec):
            ours = (matrix.parent / directive.path).resolve() == spec
            if ours:
                section.append(tlc.Spec(spec.name))
        elif ours:
            section.append(directive)
    targets = {name for d in section if isinstance(d, tlc.Check) for name in d.names}
    reaches = {f"reach:{d.operator}" for d in section if isinstance(d, tlc.Reach)}
    for mutation in mutations:
        if mutation.detects not in targets and mutation.detects not in reaches:
            stop(f"mutation '{mutation.label}': detects '{mutation.detects}', which {matrix} does not check")
    try:
        checker = tlc.Tlc()
    except tlc.Unavailable as error:
        print(error)
        sys.exit(3)
    return targets, partial(check_tla, spec, checker, tuple(tlc.execution_plan(section)))


def frozen_theorems(model):
    """Return the theorem names the model's .statements record holds."""
    record = model.with_suffix(".statements")
    if not record.is_file():
        stop(f"{record} is missing; freeze the model with lean-check.sh --freeze before checking its mutations")
    try:
        return {entry["name"] for entry in json.loads(record.read_text(encoding="utf-8"))["declarations"]
                if entry["kind"] == "theorem"}
    except (OSError, ValueError, KeyError, TypeError) as error:
        stop(f"invalid statements record {record}: {error}")


def lean_runner(model, mutations):
    """Target the frozen theorems that Lean finds public in the source, including their namespaces."""
    project = project_root(model, "lakefile.toml", "lakefile.lean")
    if project is None:
        stop(f"{model} is in no Lake project")
    frozen = frozen_theorems(model)
    toolchain = lean_toolchain(project)
    analysis = lean_analysis(model, project, toolchain)
    if analysis["errors"]:
        stop(f"unmutated Lean model does not elaborate: {analysis['errors'][0]['data']}")
    targets = {"theorem " + decl["name"] for decl in analysis["declarations"]
               if decl["theorem"] and not decl["private"] and decl["name"] in frozen
               and not is_witness(decl["name"], analysis["declarations"])}
    theorems = {(decl["name"], decl["type"]) for decl in analysis["declarations"] if decl["theorem"]}
    return targets, partial(check_lean, model, project, toolchain, theorems, analysis["commands"])


def rust_runner(model, mutations):
    project = project_root(model, "Cargo.toml")
    if project is None:
        stop(f"{model} is in no Rust crate")
    try:
        verifier = kani.Kani()
    except kani.Unavailable as error:
        print(f"UNAVAILABLE {error}")
        sys.exit(3)
    with tempfile.TemporaryDirectory(prefix="formal-kani-discover-") as temporary:
        work = Path(temporary)
        try:
            bounds = kani.discover(project, work, verifier)
            sources = verifier.source_roots(project)
            for mutation in mutations:
                if mutation.detects not in bounds:
                    stop(f"mutation '{mutation.label}': unknown harness '{mutation.detects}'")
            selected = {mutation.detects for mutation in mutations}
            for name in sorted(selected):
                outcome = kani.verify(project, work, verifier, name, bounds[name].unwind)
                if outcome.verdict is not kani.Verdict.PASS:
                    stop(f"unmutated Rust harness '{name}' did not pass: "
                         + "; ".join(outcome.failures) + "\n" + outcome.output)
        except kani.CheckError as error:
            stop(str(error))
    targets = {name for name, harness in bounds.items() if harness.source == model} | selected
    return targets, partial(check_rust, model, project, verifier, bounds, sources)


# Each runner checks the names the mutations detect, then returns the names they must cover and a check for one mutation.
# A TLA+ or Rust mutation covers the name it detects; a Lean mutation covers the theorems that fail on it.
LANGUAGES = {
    ".tla": Language("TLA+", needs_detects=True, takes_only=True, runner=tla_runner),
    ".lean": Language("Lean", needs_detects=False, takes_only=False, runner=lean_runner),
    ".rs": Language("Rust", needs_detects=True, takes_only=False, runner=rust_runner),
}


def main():
    if len(sys.argv) != 2:
        stop("usage: mutate.py <Name.mutations>", 2)
    path = Path(sys.argv[1]).resolve()
    if not path.is_file():
        stop(f"{path} does not exist")
    models = [path.with_suffix(suffix) for suffix in LANGUAGES]
    model = next((model for model in models if model.is_file()), None)
    if model is None:
        stop(f"no {', '.join(model.name for model in models[:-1])} or {models[-1].name} beside {path}")
    language, text = LANGUAGES[model.suffix], model.read_text(encoding="utf-8")
    mutations = [make_mutation(label, directives, model, text, language) for label, directives in parse(path)]
    targets, check = language.runner(model, mutations)

    detected, covered = 0, set()
    for mutation in mutations:
        with tempfile.TemporaryDirectory() as work:
            result = check(mutation, Path(work))
        if result.verdict is Verdict.ERROR:
            stop(f"mutation '{mutation.label}' did not reach a verdict:\n{result.detail.strip()}")
        detected += result.verdict is Verdict.DETECTED
        covered |= result.covers
        print(f"{result.verdict.value} {mutation.label}" + (f": {result.detail}" if result.detail else ""))
    uncovered = sorted(targets - covered)
    for name in uncovered:
        print(f"UNCOVERED {name}")
    if model.suffix == ".lean":
        print(LEAN_NOTE)
    print(f"SUMMARY {detected} of {len(mutations)} mutations detected"
          + (f", {len(uncovered)} properties without a mutation" if uncovered else ""))
    sys.exit(0 if detected == len(mutations) and not uncovered else 1)


if __name__ == "__main__":
    main()
