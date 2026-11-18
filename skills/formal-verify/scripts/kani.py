#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Run the pinned Kani and validate its versioned discovery and result records."""
import argparse
import json
import os
import re
import shutil
import sys
import tempfile
from dataclasses import dataclass
from enum import IntEnum
from pathlib import Path

sys.dont_write_bytecode = True
import workdir

STATUSES = {"Success", "Failure", "Unreachable", "Undetermined", "Satisfied", "Unsatisfiable"}
# Statuses that pass and statuses that refute the property, by check category; any other is inconclusive.
OUTCOMES = {
    "cover": ({"Satisfied"}, {"Unsatisfiable", "Unreachable"}),
    "unwind": ({"Success", "Unreachable"}, set()),
}
PROPERTY_OUTCOMES = ({"Success", "Unreachable"}, {"Failure"})


class CheckError(Exception):
    pass


class Unavailable(Exception):
    pass


class Verdict(IntEnum):
    """A check's or harness's result, ordered so the worst check decides the harness."""
    PASS = 0
    REFUTED = 1
    INCONCLUSIVE = 2


@dataclass(frozen=True)
class Harness:
    unwind: int
    source: Path


@dataclass(frozen=True)
class Outcome:
    verdict: Verdict
    checks: int
    failures: list
    output: str


def search_path(inherited, *directories):
    entries = [str(directory) for directory in directories]
    if inherited is not None:
        entries.append(inherited)
    return os.pathsep.join(entries)


@dataclass(frozen=True)
class CargoMetadata:
    workspace: Path
    target: Path
    packages: tuple


@dataclass
class CrateSources:
    roots: set
    outputs: set

    def stage(self, crate, destination):
        """Copy local packages in their relative layout, omitting Cargo's build directories."""
        anchor = Path(os.path.commonpath(self.roots))

        def ignore(directory, names):
            # Cargo tags each build directory, including one left behind after the target directory moved.
            return [name for name in names if name == ".git" or Path(directory) / name in self.outputs
                    or (Path(directory) / name / "CACHEDIR.TAG").is_file()]

        for root in self.roots:
            if self.roots.isdisjoint(root.parents):
                shutil.copytree(root, destination / root.relative_to(anchor), ignore=ignore)
        return destination / crate.relative_to(anchor)


class Kani:
    version = "0.68.0"

    def __init__(self):
        home = Path(os.environ.get("KANI_HOME", Path.home() / ".kani")).resolve()
        self.timeout = os.environ.get("KANI_HARNESS_TIMEOUT", "").strip() or "5m"
        limit = re.fullmatch(r"\+?0*([1-9][0-9]{0,9})([smh]?)", self.timeout)
        if not limit or int(limit[1]) >= 2**32:
            raise Unavailable(f"KANI_HARNESS_TIMEOUT={self.timeout!r} is not a harness time limit; set a whole "
                              "number from 1 to 4294967295 with an optional unit s, m or h, such as 90s or 20m, "
                              "or unset it for five minutes")
        # Kani reads a number with no unit as seconds; name the unit when reporting the limit.
        self.limit = limit[1] + (limit[2] or "s")
        bundle = home / f"kani-{self.version}"
        remedy = (f"run cargo install --locked kani-verifier --version {self.version} "
                  "then cargo kani setup")
        for binary in ("bin/kani-driver", "bin/kani-compiler", "bin/cbmc", "toolchain/bin/rustc", "toolchain/bin/cargo"):
            path = bundle / binary
            if not path.is_file() or not os.access(path, os.X_OK):
                raise Unavailable(f"Kani {self.version} bundle is incomplete; {remedy}")
        if any(home.glob("*.tar.gz")):
            raise Unavailable(f"incomplete Kani setup at {home}; finish cargo kani setup before checking")
        self.bundle = bundle
        self.driver = bundle / "bin/kani-driver"
        self.cargo = bundle / "toolchain/bin/cargo"
        self.env = os.environ | {
            "KANI_HOME": str(home),
            "RUSTUP_TOOLCHAIN": str((bundle / "toolchain").resolve()),
            "PATH": search_path(os.environ.get("PATH"), bundle / "bin", bundle / "pyroot/bin", bundle / "toolchain/bin"),
            "PYTHONPATH": search_path(os.environ.get("PYTHONPATH"), bundle / "pyroot"),
        }
        # A parent cargo (cargo run, cargo test, a build script) exports its rustup toolchain's
        # lib directory here; the bundled compiler must load only the bundled toolchain.
        loader = "DYLD_FALLBACK_LIBRARY_PATH" if sys.platform == "darwin" else "LD_LIBRARY_PATH"
        if loader in self.env:
            self.env[loader] = os.pathsep.join(
                path for path in self.env[loader].split(os.pathsep)
                if not (Path(path).name == "lib" and Path(path).parent.parent.name == "toolchains"))
        try:
            done = self.run("--version")
        except CheckError as error:
            raise Unavailable(f"Kani {self.version} cannot run: {error}; {remedy}") from error
        if done.returncode or not done.stdout.startswith(f"Kani Rust Verifier {self.version} (cargo plugin)\n"):
            raise Unavailable(f"Kani {self.version} is required; {remedy}")

    def run(self, *arguments, cwd=None):
        try:
            # The driver selects Cargo mode from argv[0]; the Cargo wrapper can auto-install.
            return workdir.run_captured(["cargo-kani", *arguments], executable=str(self.driver), env=self.env, cwd=cwd)
        except OSError as error:
            raise CheckError(f"cannot execute Kani: {error}") from error

    def cargo_metadata(self, crate, resolve=False):
        """Read package declarations; resolve only when finding the full local source graph."""
        try:
            done = workdir.run_captured(
                [str(self.cargo), "metadata", *([] if resolve else ["--no-deps"]), "--format-version", "1",
                 "--manifest-path", str(crate / "Cargo.toml")],
                cwd=crate, env=self.env)
        except OSError as error:
            raise CheckError(f"cannot read Cargo metadata: {error}") from error
        if done.returncode:
            raise CheckError(f"Cargo metadata failed for {crate}:\n{done.stdout}{done.stderr}")
        try:
            report = json.loads(done.stdout)
            if report["version"] != 1:
                raise CheckError("unsupported Cargo metadata version")
            workspace = Path(report["workspace_root"])
            target = Path(report["target_directory"])
            packages = []
            for package in report["packages"]:
                if package["source"] is None:
                    packages.append(Path(package["manifest_path"]).parent)
                    packages.extend(Path(dep["path"]) for dep in package["dependencies"] if "path" in dep)
            if not all(path.is_absolute() for path in (workspace, target, *packages)):
                raise CheckError("Cargo metadata returned a relative source path")
            return CargoMetadata(workspace, target, tuple(packages))
        except (ValueError, KeyError, TypeError) as error:
            raise CheckError(f"malformed Cargo metadata: {error}") from error

    def crate_sources(self, crate):
        """Find local workspaces, including transitive and optional path dependencies."""
        pending, visited = {crate}, set()
        sources = CrateSources(set(), set())
        while pending:
            directory = pending.pop()
            if directory in visited:
                continue
            visited.add(directory)
            metadata = self.cargo_metadata(directory, resolve=directory == crate)
            sources.roots.update((metadata.workspace.resolve(), directory))
            sources.outputs.add(metadata.target.parent.resolve() / metadata.target.name)
            pending.update(path.resolve() for path in metadata.packages)
        return sources


def invoke(crate, work, kani, *arguments, cwd=None):
    return kani.run("--manifest-path", str(crate / "Cargo.toml"),
                    "--target-dir", str(work / "target"), "-Z", "stubbing", *arguments, cwd=cwd or crate)


def read_json(path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise CheckError(f"missing or invalid Kani report {path.name}: {error}") from error


def discover(crate, work, kani):
    """Compile current harness metadata without `list`, which writes into the source directory."""
    if not (crate / "Cargo.toml").is_file():
        raise CheckError(f"{crate}/Cargo.toml is missing")
    workspace = kani.cargo_metadata(crate).workspace
    done = invoke(crate, work, kani, "--only-codegen")
    if done.returncode:
        output = done.stdout + done.stderr
        if "error[E0658]" in output:
            try:
                toolchain = (kani.bundle / "rust-toolchain-version").read_text(encoding="utf-8").strip()
            except OSError:
                toolchain = "Rust toolchain (version metadata unavailable)"
            output += (f"\nKani {kani.version} compiles with its bundled {toolchain}, which lacks a feature "
                       "used at the locations above. Rewrite harness code that uses it. If every location is "
                       "in production code or a dependency, report the Kani target as not checked; a feature "
                       "attribute would change the production crate.")
        raise CheckError(f"Kani discovery failed:\n{output}")
    harnesses = {}
    try:
        for metadata in (work / "target").rglob("*.kani-metadata.json"):
            for harness in read_json(metadata)["proof_harnesses"]:
                if harness["attributes"]["kind"] != "Proof":
                    continue
                name = harness["pretty_name"]
                bound = harness["attributes"].get("unwind_value")
                source = harness["original_file"]
                if not isinstance(name, str) or not name or not isinstance(source, str) or not source:
                    raise CheckError("malformed Kani harness name or source")
                if name in harnesses:
                    raise CheckError("duplicate harness names; select a single crate")
                if type(bound) is not int or bound < 1:
                    raise CheckError(f"{name} needs #[kani::unwind(N)] with N greater than zero")
                harnesses[name] = Harness(bound, (workspace / source).resolve())
    except (KeyError, TypeError, AttributeError) as error:
        raise CheckError(f"malformed Kani discovery record: {error!r}") from error
    if not harnesses:
        raise CheckError("no proof harnesses found")
    return harnesses


def harness_result(report, kani, name, returncode):
    """Return the one harness result in report after checking it agrees with itself and the process."""
    if report.get("metadata", {}).get("version") != "1.0" or report["metadata"].get("kani_version") != kani.version:
        raise CheckError("unsupported Kani result schema or version")
    if any(detail.get("harness_id") == name and detail.get("exit_status") == "timeout"
           for detail in report.get("error_details", [])):
        raise CheckError(f"the solver did not finish within the {kani.limit} harness limit; "
                         "narrow the harness or set KANI_HARNESS_TIMEOUT to a longer limit")
    verification = report["verification_results"]
    summary, results = verification["summary"], verification["results"]
    if summary["status"] != "completed" or summary["executed"] != 1 or summary["total_harnesses"] != 1:
        raise CheckError("incomplete Kani verification")
    if len(results) != 1 or results[0]["harness_id"] != name:
        raise CheckError("Kani returned an unexpected harness")
    result = results[0]
    if not isinstance(result["checks"], list) or not result["checks"]:
        raise CheckError("Kani returned no property checks")
    if result["status"] not in {"Success", "Failure"}:
        raise CheckError("unknown Kani harness status")
    failed = result["status"] == "Failure"
    if returncode != int(failed) or summary["failed"] != int(failed) or summary["successful"] != int(not failed):
        raise CheckError("Kani process and result disagree")
    return result


def classify(check):
    category, status = check["category"], check["status"]
    if status not in STATUSES:
        raise CheckError(f"unknown Kani check status {status}")
    passes, refutes = OUTCOMES.get(category, PROPERTY_OUTCOMES)
    if status in passes:
        return Verdict.PASS
    return Verdict.REFUTED if status in refutes else Verdict.INCONCLUSIVE


def describe(check):
    location = check["location"]
    reason = "bound too low: " if check["category"] == "unwind" else ""
    return (f"{reason}{check['category']} {check['status']}: {check['description']} at "
            f"{location['file']}:{location['line']}:{location['column']}")


def verify(crate, work, kani, name, bound, *, cwd=None):
    """Check one harness; a report that is malformed or disagrees with the process is inconclusive."""
    result_file = work / "result.json"
    result_file.unlink(missing_ok=True)
    try:
        done = invoke(crate, work, kani, "--harness", name, "--exact", "--unwind", str(bound),
                      "-Z", "unstable-options", "--harness-timeout", kani.timeout,
                      "--export-json", str(result_file),
                      "-Z", "concrete-playback", "--concrete-playback", "print",
                      "--output-format", "regular", cwd=cwd)
    except CheckError as error:
        return Outcome(Verdict.INCONCLUSIVE, 0, [str(error)], "")
    output = done.stdout + done.stderr
    try:
        result = harness_result(read_json(result_file), kani, name, done.returncode)
        verdicts = [(check, classify(check)) for check in result["checks"]]
        verdict = max(verdict for _, verdict in verdicts)
        if verdict is Verdict.PASS and result["status"] != "Success":
            raise CheckError("Kani reports a harness failure that no check explains")
        if verdict is Verdict.PASS and not any(
                check["status"] == "Satisfied" and check["category"] == "cover"
                for check, _ in verdicts):
            # Kani labels compiler safety checks as assertions too: an overflow check
            # before contradictory assumptions can succeed while the property is unreachable.
            raise CheckError("no satisfied kani::cover! witness; cover a boundary after the assumptions")
        failures = [describe(check) for check, verdict in verdicts if verdict is not Verdict.PASS]
    except (KeyError, TypeError, AttributeError, CheckError) as error:
        return Outcome(Verdict.INCONCLUSIVE, 0, [f"verification did not complete: {error}"], output)
    return Outcome(verdict, len(verdicts), failures, output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("ready", help="check that the pinned Kani bundle runs")
    check = commands.add_parser("check", help="verify the crate's proof harnesses")
    check.add_argument("crate")
    check.add_argument("harnesses", nargs="*")
    arguments = parser.parse_args()
    try:
        kani = Kani()
    except Unavailable as error:
        print(f"UNAVAILABLE {error}")
        return 3
    if arguments.command == "ready":
        print(f"READY Kani {kani.version}")
        return 0
    crate, selected = Path(arguments.crate).resolve(), arguments.harnesses
    workdir.warn_runtime()
    try:
        with workdir.signal_cleanup(), tempfile.TemporaryDirectory(prefix="formal-kani-", dir=workdir.ensure_temp_root()) as temporary:
            work = Path(temporary)
            try:
                bounds = discover(crate, work, kani)
                names = list(dict.fromkeys(selected)) if selected else sorted(bounds)
                unknown = set(names) - set(bounds)
                if unknown:
                    raise CheckError("unknown harnesses: " + ", ".join(sorted(unknown)))
            except CheckError as error:
                print(f"FAIL {error}")
                return 1
            passed = 0
            for name in names:
                outcome = verify(crate, work, kani, name, bounds[name].unwind)
                ok = outcome.verdict is Verdict.PASS
                passed += ok
                print(f"{'PASS' if ok else 'FAIL'} {name} unwind={bounds[name].unwind} checks={outcome.checks}"
                      + (": " + "; ".join(outcome.failures) if outcome.failures else ""))
                if not ok:
                    print(outcome.output.rstrip())
            print(f"SUMMARY {passed} of {len(names)} harnesses passed")
            return 0 if passed == len(names) else 1
    except workdir.SignalTerminated as error:
        return error.status


if __name__ == "__main__":
    sys.exit(main())
