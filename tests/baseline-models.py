# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Check that the baseline rejects specification narrowing that makes real verifier failures pass."""
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "skills/formal-verify/scripts"
EXAMPLES = ROOT / "skills/formal-verify/examples"


def run(status, script, *arguments):
    interpreter = "python3" if script.endswith(".py") else "bash"
    # TLC extracts standard modules under java.io.tmpdir and deletes them on exit.
    with tempfile.TemporaryDirectory(prefix="formal-java-") as java_work:
        options = f'{os.environ.get("JAVA_TOOL_OPTIONS", "")} -Djava.io.tmpdir="{java_work}"'
        done = subprocess.run([interpreter, str(SCRIPTS / script), *map(str, arguments)],
                              env=os.environ | {"JAVA_TOOL_OPTIONS": options}, capture_output=True, text=True, check=False)
    print(done.stdout + done.stderr, end="", flush=True)
    if done.returncode != status:
        raise RuntimeError(f"{script} exited {done.returncode}, expected {status}")
    return done.stdout


def matrix_order(work):
    project = work / "tla"
    shutil.copytree(EXAMPLES / "tla-template", project)
    matrix, spec, record = project / "BoundedQueue.matrix", project / "BoundedQueue.tla", work / "tla.json"
    checks = "check INVARIANTS TypeOK InWindow\ncheck PROPERTIES AllConsumed\n"
    runs = "run one | Window=1 Items=3 Workers={w1} FailAt={}\n"
    matrix.write_text("spec BoundedQueue.tla\n" + checks + runs)
    run(0, "tlc-matrix.sh", matrix)
    run(0, "baseline.py", "record", record, matrix)
    spec.write_text(spec.read_text().replace("next < consumed + Window", "next <= consumed + Window"))
    run(1, "tlc-matrix.sh", matrix)
    matrix.write_text("spec BoundedQueue.tla\n" + runs + checks)
    changed = run(1, "baseline.py", "compare", record)
    assert "removed check BoundedQueue.tla INVARIANTS InWindow | [run BoundedQueue.tla one]" in changed
    run(0, "tlc-matrix.sh", matrix)


def imported_property(work):
    project = work / "imports"
    project.mkdir()
    rules, matrix = project / "Rules.tla", project / "Advance.matrix"
    rules.write_text("---- MODULE Rules ----\nAllowed(x) == x = 0\n====\n")
    (project / "Advance.tla").write_text(r"""---- MODULE Advance ----
EXTENDS Rules
VARIABLE x
Init == x = 0
Next == x' = 1
Spec == Init /\ [][Next]_x
Within == Allowed(x)
====
""")
    matrix.write_text("spec Advance.tla\ncheck INVARIANT Within\nrun default |\n")
    record = work / "imports.json"
    run(0, "baseline.py", "record", record, matrix)
    assert "Invariant Within is violated" in run(1, "tlc-matrix.sh", matrix)
    rules.write_text(rules.read_text().replace("x = 0", "TRUE"))
    run(0, "tlc-matrix.sh", matrix)
    assert "changed definition Rules.tla Allowed" in run(1, "baseline.py", "compare", record)


def fairness_subscript(work):
    plain = r"Spec == Init /\ [][Next]_vars /\ WF_vars(Next)"
    quantified = "Step(p) == Next\n" + r"Spec == Init /\ [][Next]_<<x, aux>> /\ \A p \in {1} : WF_vars(Step(p))"
    for name, fairness in (("subscript", plain), ("quantified", quantified)):
        project = work / name
        project.mkdir()
        spec, matrix, record = project / "One.tla", project / "One.matrix", work / f"{name}.json"
        spec.write_text(r"""---- MODULE One ----
EXTENDS Naturals
VARIABLES x, aux
vars == <<x, aux>>
Init == x = 0 /\ aux = 0
Inc == x < 3 /\ x' = x + 1 /\ UNCHANGED aux
Spin == aux' = 1 - aux /\ UNCHANGED x
Next == Inc \/ Spin
""" + fairness + """
Done == <>(x = 3)
====
""")
        matrix.write_text("spec One.tla\ncheck PROPERTIES Done\nrun base |\n")
        assert "Temporal properties were violated" in run(1, "tlc-matrix.sh", matrix)
        run(0, "baseline.py", "record", record, matrix)
        spec.write_text(spec.read_text().replace("vars == <<x, aux>>", "vars == <<x>>"))
        run(0, "tlc-matrix.sh", matrix)
        assert "changed definition One.tla vars" in run(1, "baseline.py", "compare", record)


def tla_layout(work):
    project = work / "layout"
    project.mkdir()
    spec, matrix = project / "Layout.tla", project / "Layout.matrix"
    matrix.write_text("spec Layout.tla\ncheck INVARIANT Safe\nrun one |\n")
    prefix = "---- MODULE Layout ----\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\nSpec == Init /\\ [][Next]_x\n"
    grouped = r"""Safe ==
    \/ /\ x = 1
       /\ \/ x = 1
          \/ x = 1
          \/ x = 0
"""
    helper = "Unused == FALSE\n  Allowed(n) == n = 1\nSafe == Allowed(x)\n"
    cases = [
        (grouped, grouped.replace("          \\/ x = 0", "    \\/ x = 0")),
        (helper, helper.replace("n = 1", "n = 0")),
    ]
    for before, after in cases:
        spec.write_text(prefix + before + "====\n")
        run(0, "baseline.py", "record", work / "layout.json", matrix)
        assert "Invariant Safe is violated" in run(1, "tlc-matrix.sh", matrix)
        spec.write_text(prefix + after + "====\n")
        run(0, "tlc-matrix.sh", matrix)
        run(1, "baseline.py", "compare", work / "layout.json")


def kani_ownership(work):
    project = work / "kani"
    (project / "src").mkdir(parents=True)
    shutil.copyfile(EXAMPLES / "kani-template/Cargo.toml", project / "Cargo.toml")
    source, record = project / "src/lib.rs", work / "kani.json"
    before = """pub fn target(n: u8) -> u8 { n }
#[cfg(kani)]
mod proofs {
    #[kani::proof]
    #[kani::unwind(2)]
    fn bounded_support() {
        let n: u8 = kani::any();
        kani::assume(n < 10);
        assert!(u16::from(n) < 256);
        kani::cover!(n == 9);
    }
    #[kani::proof]
    #[kani::unwind(2)]
    fn target_preserves_input() {
        let n: u8 = kani::any();
        assert!(super::target(n) == n);
        kani::cover!(n == 9);
    }
}
"""
    source.write_text(before)
    run(0, "kani-check.sh", project)
    run(0, "baseline.py", "record", record, source)
    broken = before.replace("{ n }", "{ if n < 10 { n } else { 0 } }")
    source.write_text(broken)
    run(1, "kani-check.sh", project)
    moved = broken.replace("        kani::assume(n < 10);\n", "")
    moved = moved.replace("        assert!(super::target(n) == n);", "        kani::assume(n < 10);\n        assert!(super::target(n) == n);")
    source.write_text(moved)
    changed = run(1, "baseline.py", "compare", record)
    assert "added assume n < 10 in proofs::target_preserves_input" in changed
    assert "removed assume n < 10 in proofs::bounded_support" in changed
    run(0, "kani-check.sh", project)


with tempfile.TemporaryDirectory(prefix="formal-baseline-") as directory:
    tla_layout(Path(directory))
    matrix_order(Path(directory))
    imported_property(Path(directory))
    fairness_subscript(Path(directory))
    kani_ownership(Path(directory))
print("ok: the baseline rejects narrowed checks and assumptions even when the real verifiers pass")
