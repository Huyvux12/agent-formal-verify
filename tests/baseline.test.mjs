// Copyright (c) 2026 Michael Denyer
// SPDX-License-Identifier: GPL-3.0-only
import assert from "node:assert/strict";
import { copyFileSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { afterEach, test } from "node:test";
import { fixture, removeFixtures, root, run } from "./helpers.mjs";

afterEach(removeFixtures);

const examples = join(root, "skills/formal-verify/examples");

function models() {
  const dir = realpathSync(fixture());
  for (const folder of ["tla", "lean", "kani"]) mkdirSync(join(dir, folder));
  const paths = {
    matrix: join(dir, "tla/BoundedQueue.matrix"),
    spec: join(dir, "tla/BoundedQueue.tla"),
    statements: join(dir, "lean/BoundedQueue.statements"),
    rust: join(dir, "kani/lib.rs"),
    record: join(dir, "record.json"),
  };
  copyFileSync(join(examples, "tla-template/BoundedQueue.matrix"), paths.matrix);
  copyFileSync(join(examples, "tla-template/BoundedQueue.tla"), paths.spec);
  copyFileSync(join(examples, "lean-template/Model/BoundedQueue.statements"), paths.statements);
  copyFileSync(join(examples, "kani-template/src/lib.rs"), paths.rust);
  return { dir, ...paths };
}

const baseline = (dir, ...args) => run(dir, "baseline.py", args);
const lines = (result) => result.stdout.split("\n").filter(Boolean);

function edit(path, from, to) {
  const text = readFileSync(path, "utf8");
  assert.ok(text.includes(from), `${path} lacks ${JSON.stringify(from)}`);
  writeFileSync(path, text.replace(from, to));
}

function rewriteStatements(path, change) {
  const record = JSON.parse(readFileSync(path, "utf8"));
  change(record);
  writeFileSync(path, JSON.stringify(record, null, 2) + "\n");
}

function recordedThenEdited(setup, target, change) {
  const files = models();
  setup?.(files);
  assert.equal(baseline(files.dir, "record", files.record, files[target]).status, 0);
  change(files);
  const result = baseline(files.dir, "compare", files.record);
  return { files, result, out: lines(result) };
}

function assertChanged({ files, result, out }, target, ...details) {
  assert.equal(result.status, 1);
  assert.equal(out[0], `CHANGED ${files[target]}`);
  assert.equal(out.at(-1), "SUMMARY 0 unchanged, 1 changed");
  for (const detail of details) assert.ok(out.some((line) => line.includes(detail)), `${JSON.stringify(out)} lacks ${detail}`);
}

function assertUnchanged({ files, result, out }, target) {
  assert.equal(result.status, 0);
  assert.deepEqual(out, [`UNCHANGED ${files[target]}`, "SUMMARY 1 unchanged, 0 changed"]);
}

const tla = (from, to) => (change) => edit(change.spec, from, to);
const rust = (from, to) => (change) => edit(change.rust, from, to);

test("a re-frozen Lean declaration is changed and named, whichever hash moved", () => {
  for (const field of ["typeHash", "valueHash"]) {
    const outcome = recordedThenEdited(null, "statements", ({ statements }) =>
      rewriteStatements(statements, (record) => {
        record.declarations.find((entry) => entry.name === "BoundedQueue.Invariant")[field] = "0".repeat(64);
      }));
    assertChanged(outcome, "statements", "changed declaration BoundedQueue.Invariant");
  }
});

test("a Lean declaration added after the record is allowed", () => {
  const outcome = recordedThenEdited(null, "statements", ({ statements }) =>
    rewriteStatements(statements, (record) => {
      record.declarations.push({ name: "BoundedQueue.helper", kind: "theorem", type: "True", typeHash: "1".repeat(64), valueHash: null });
    }));
  assertUnchanged(outcome, "statements");
});

test("a removed Lean declaration and a changed toolchain are changed", () => {
  const removed = recordedThenEdited(null, "statements", ({ statements }) =>
    rewriteStatements(statements, (record) => {
      record.declarations = record.declarations.filter((entry) => entry.name !== "BoundedQueue.claim");
    }));
  assertChanged(removed, "statements", "removed declaration BoundedQueue.claim");
  const toolchain = recordedThenEdited(null, "statements", ({ statements }) =>
    rewriteStatements(statements, (record) => {
      record.toolchain = "leanprover/lean4:v4.0.0";
    }));
  assertChanged(toolchain, "statements", "changed toolchain");
});

test("a TLA+ check line that loses a property is changed", () => {
  const outcome = recordedThenEdited(null, "matrix", ({ matrix }) => edit(matrix, "check INVARIANTS TypeOK InWindow", "check INVARIANTS TypeOK"));
  assertChanged(outcome, "matrix", "removed check BoundedQueue.tla INVARIANTS InWindow");
});

test("moving TLA+ checks below their runs loses those runs' guarantees", () => {
  const outcome = recordedThenEdited(null, "matrix", ({ matrix }) => {
    const text = readFileSync(matrix, "utf8");
    const checks = text.split("\n").filter((line) => line.startsWith("check "));
    writeFileSync(matrix, text.split("\n").filter((line) => !line.startsWith("check ")).join("\n") + checks.join("\n") + "\n");
  });
  assertChanged(outcome, "matrix", "removed check BoundedQueue.tla INVARIANTS InWindow");
});

test("a TLA+ reach check records the first matching run's inputs", () => {
  const setup = ({ matrix }) => edit(matrix, "reach WindowFull | window=1", "reach WindowFull | window=");
  const outcome = recordedThenEdited(setup, "matrix", ({ matrix }) => {
    const text = readFileSync(matrix, "utf8");
    const runs = text.split("\n").filter((line) => line.startsWith("run "));
    writeFileSync(matrix, text.split("\n").filter((line) => !line.startsWith("run ")).join("\n") + runs.reverse().join("\n") + "\n");
  });
  assertChanged(outcome, "matrix", "changed reach BoundedQueue.tla WindowFull");
});

test("repeated TLA+ spec sections keep their checks attached to their own runs", () => {
  const setup = ({ matrix }) => writeFileSync(matrix, [
    "spec BoundedQueue.tla", "check INVARIANTS TypeOK InWindow", "run first | Window=1 Items=3",
    "spec BoundedQueue.tla", "check INVARIANTS TypeOK", "run second | Window=2 Items=3", "",
  ].join("\n"));
  const outcome = recordedThenEdited(setup, "matrix", ({ matrix }) => {
    edit(matrix, "check INVARIANTS TypeOK InWindow", "check INVARIANTS TypeOK");
    edit(matrix, "run second", "check INVARIANTS InWindow\nrun second");
  });
  assertChanged(outcome, "matrix", "removed check BoundedQueue.tla INVARIANTS InWindow | [run BoundedQueue.tla first]");
});

test("adding a TLA+ check strengthens an existing run without changing its baseline", () => {
  const setup = ({ matrix }) => edit(matrix, "check INVARIANTS TypeOK InWindow", "check INVARIANTS TypeOK");
  const outcome = recordedThenEdited(setup, "matrix", ({ matrix }) => edit(matrix, "check INVARIANTS TypeOK", "check INVARIANTS TypeOK InWindow"));
  assertUnchanged(outcome, "matrix");
});

test("duplicate TLA+ checks cannot stand in for a check on a different occurrence of the same run label", () => {
  const section = "spec BoundedQueue.tla\ncheck INVARIANTS TypeOK InWindow\nrun same | Window=1 Items=3\n";
  const setup = ({ matrix }) => writeFileSync(matrix, section + section);
  const outcome = recordedThenEdited(setup, "matrix", ({ matrix }) => writeFileSync(matrix,
    section.replace("TypeOK InWindow", "TypeOK InWindow InWindow") + section.replace("TypeOK InWindow", "TypeOK")));
  assertChanged(outcome, "matrix", "removed check BoundedQueue.tla INVARIANTS InWindow");
});

test("an unedited matrix that repeats a spec section compares unchanged", () => {
  const section = "spec BoundedQueue.tla\ncheck INVARIANTS TypeOK InWindow\nrun same | Window=1 Items=3\n";
  const setup = ({ matrix }) => writeFileSync(matrix, section + section);
  assertUnchanged(recordedThenEdited(setup, "matrix", () => {}), "matrix");
});

test("a TLA+ Spec that loses fairness is changed", () => {
  assertChanged(recordedThenEdited(null, "matrix", tla(" /\\ WF_vars(Consume)", "")), "matrix", "changed definition BoundedQueue.tla Spec");
});

test("a weakened TLA+ property is changed", () => {
  const outcome = recordedThenEdited(null, "matrix", tla("next <= consumed + Window", "next <= consumed + Window + 1"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla InWindow");
});

test("a TLA+ helper that a property references is changed, and an action that none references is not", () => {
  const helper = tla("AllConsumed == <>(consumed = Items)", "Finished == consumed = Items\nAllConsumed == <>Finished");
  const outcome = recordedThenEdited(helper, "matrix", tla("Finished == consumed = Items", "Finished == consumed >= 0"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla Finished");
  assertUnchanged(recordedThenEdited(null, "matrix", tla("next' = next + 1", "next' = next + 2")), "matrix");
});

test("a TLA+ operator that only a function definition's domain references is changed", () => {
  const helper = tla("InWindow == consumed <= next /\\ next <= consumed + Window",
    "Slots == 0..Window\nFits[k \\in Slots] == next <= consumed + k\nInWindow == consumed <= next /\\ \\E k \\in DOMAIN Fits : Fits[k]");
  const outcome = recordedThenEdited(helper, "matrix", tla("Slots == 0..Window", "Slots == 0..Items"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla Slots");
});

test("TLA+ properties follow transitive local imports and leave unrelated action bodies free to change", () => {
  function setup(files) {
    edit(files.spec, "EXTENDS Naturals", "EXTENDS Naturals,\n  Predicates");
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "AllConsumed == <>Finished(consumed, Items)");
    writeFileSync(join(files.dir, "tla/Predicates.tla"),
      "---- MODULE Predicates ----\nEXTENDS Limits\nFinished(n, total) == Equal(n, total)\n====\n");
    writeFileSync(join(files.dir, "tla/Limits.tla"),
      "---- MODULE Limits ----\nEqual(n, m) == n = m\nOtherAction == TRUE\n====\n");
  }
  const change = (from, to) => ({ dir }) => edit(join(dir, "tla/Limits.tla"), from, to);
  assertChanged(recordedThenEdited(setup, "matrix", change("n = m", "TRUE")), "matrix", "changed definition Limits.tla Equal");
  assertUnchanged(recordedThenEdited(setup, "matrix", change("OtherAction == TRUE", "OtherAction == FALSE")), "matrix");
});

test("a multi-line LOCAL definition with a tab after LOCAL does not hide the imported operator of that name", () => {
  function setup(files) {
    edit(files.spec, "EXTENDS Naturals", "EXTENDS Naturals, Shared, Hidden");
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "AllConsumed == <>Finished(consumed, Items)");
    writeFileSync(join(files.dir, "tla/Shared.tla"), "---- MODULE Shared ----\nFinished(n, total) == n = total\n====\n");
    writeFileSync(join(files.dir, "tla/Hidden.tla"), "---- MODULE Hidden ----\nLOCAL\tFinished(n, total) ==\n  TRUE\n====\n");
  }
  assertChanged(recordedThenEdited(setup, "matrix", ({ dir }) => edit(join(dir, "tla/Shared.tla"), "n = total", "TRUE")),
    "matrix", "changed definition Shared.tla Finished");
});

test("a locally imported operator with an indented header is tracked", () => {
  const setup = (files) => {
    edit(files.spec, "EXTENDS Naturals", "EXTENDS Naturals, Limits");
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "AllConsumed == <>Equal(consumed, Items)");
    writeFileSync(join(files.dir, "tla/Limits.tla"), "---- MODULE Limits ----\n  Equal(n, m) == n = m\n====\n");
  };
  assertChanged(recordedThenEdited(setup, "matrix", ({ dir }) =>
    edit(join(dir, "tla/Limits.tla"), "n = m", "TRUE")), "matrix", "Limits.tla");
});

test("a local TLA+ instance retains both its operator bodies and its substitutions", () => {
  function setup(files) {
    edit(files.spec, "AllConsumed == <>(consumed = Items)",
      "Bounds == INSTANCE Limit WITH Max <- Items\nAllConsumed == <>Bounds!Finished(consumed)");
    writeFileSync(join(files.dir, "tla/Limit.tla"),
      "---- MODULE Limit ----\nCONSTANT Max\nFinished(n) == n = Max\n====\n");
  }
  assertChanged(recordedThenEdited(setup, "matrix", ({ dir }) =>
    edit(join(dir, "tla/Limit.tla"), "n = Max", "TRUE")), "matrix", "Limit.tla");
  assertChanged(recordedThenEdited(setup, "matrix", tla("Max <- Items", "Max <- Window")), "matrix", "BoundedQueue.tla");
});

test("pre-import TLA+ baselines require review and can be recorded again", () => {
  const files = models();
  assert.equal(baseline(files.dir, "record", files.record, files.matrix).status, 0);
  const record = JSON.parse(readFileSync(files.record, "utf8"));
  delete record.models[files.matrix].surface["imports BoundedQueue.tla"];
  writeFileSync(files.record, JSON.stringify(record));
  const compared = baseline(files.dir, "compare", files.record);
  assert.equal(compared.status, 1);
  assert.match(compared.stdout, /previous baseline did not track imported modules/);
  assert.equal(baseline(files.dir, "record", files.record, files.matrix).status, 0);
  assert.equal(baseline(files.dir, "compare", files.record).status, 0);
});

test("a pre-layout TLA+ record requires review even if the model has only single-line definitions", () => {
  const files = models();
  assert.equal(baseline(files.dir, "record", files.record, files.matrix).status, 0);
  const record = JSON.parse(readFileSync(files.record, "utf8"));
  delete record.models[files.matrix].surface["TLA+ layout version"];
  writeFileSync(files.record, JSON.stringify(record));
  const result = baseline(files.dir, "compare", files.record);
  assert.equal(result.status, 1);
  assert.match(result.stdout, /did not preserve TLA\+ layout/);
});

test("indented LET definitions keep per-definition records for actions and properties", () => {
  const setup = (files) => {
    edit(files.spec, "         /\\ next' = next + 1", "         /\\ LET step == 1\n            IN next' = next + step");
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "AllConsumed ==\n    LET done == consumed = Items\n    IN <>done");
  };
  assertUnchanged(recordedThenEdited(setup, "matrix", tla("step == 1", "step == 2")), "matrix");
  assertChanged(recordedThenEdited(setup, "matrix", tla("done == consumed = Items", "done == consumed >= 0")),
    "matrix", "changed definition BoundedQueue.tla AllConsumed");
});

test("a nested LET closes only its own scope, so a later definition of the outer LET stays local", () => {
  const setup = tla("AllConsumed == <>(consumed = Items)",
    "AllConsumed ==\n    LET done == LET all == Items IN consumed = all\n        also == TRUE\n    IN <>(done /\\ also)");
  assertChanged(recordedThenEdited(setup, "matrix", tla("also == TRUE", "also == FALSE")),
    "matrix", "changed definition BoundedQueue.tla AllConsumed");
});

test("an imported module with an indented LET definition keeps per-definition records", () => {
  const setup = (files) => {
    edit(files.spec, "EXTENDS Naturals", "EXTENDS Naturals, Limits");
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "AllConsumed == <>Equal(consumed, Items)");
    writeFileSync(join(files.dir, "tla/Limits.tla"),
      "---- MODULE Limits ----\nEqual(n, m) ==\n  LET same == n = m IN same\nOtherAction == TRUE\n====\n");
  };
  const change = (from, to) => ({ dir }) => edit(join(dir, "tla/Limits.tla"), from, to);
  assertChanged(recordedThenEdited(setup, "matrix", change("same == n = m", "same == TRUE")), "matrix", "changed definition Limits.tla Equal");
  assertUnchanged(recordedThenEdited(setup, "matrix", change("OtherAction == TRUE", "OtherAction == FALSE")), "matrix");
});

test("an indented TLA+ definition after a LET closes, or a column-0 one inside a LET, compares the whole module", () => {
  for (const replacement of [
    "Unused ==\n  LET one == 1 IN one\n  Finished == consumed = Items\nAllConsumed == <>Finished",
    "AllConsumed ==\n  LET\nFinished == consumed = Items\n  IN <>Finished",
    "AllConsumed ==\n  LET Finished == consumed = Items\na ++ b == a + b\n  IN <>Finished",
  ]) {
    const setup = tla("AllConsumed == <>(consumed = Items)", replacement);
    assertChanged(recordedThenEdited(setup, "matrix", tla("Finished == consumed = Items", "Finished == TRUE")),
      "matrix", "changed module text");
  }
});

test("a TLA+ Init that Spec narrows is changed", () => {
  assertChanged(recordedThenEdited(null, "matrix", tla("Init == next = 0 /\\ consumed = 0", "Init == next = 0 /\\ consumed = 0 /\\ Items = 0")), "matrix", "changed definition BoundedQueue.tla Init");
});

test("an edit on an unindented continuation line of a TLA+ property is changed", () => {
  const unindented = tla("InWindow == consumed <= next /\\ next <= consumed + Window", "InWindow ==\nconsumed <= next /\\\nnext <= consumed + Window");
  const outcome = recordedThenEdited(unindented, "matrix", tla("\nnext <= consumed + Window", "\nnext <= consumed + Window + 1"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla InWindow");
});

test("a TLA+ operator with an operator parameter is its own recorded definition", () => {
  const higherOrder = (files) => {
    edit(files.spec, "InWindow == consumed <= next /\\ next <= consumed + Window", "InWindow == consumed <= next /\\ next <= consumed + Window /\\ Holds(Bounded)");
    edit(files.spec, "\nSpec ==", "\nBounded(n) == n >= 0\nHolds(P(_)) == P(next)\n\nSpec ==");
  };
  const outcome = recordedThenEdited(higherOrder, "matrix", tla("Holds(P(_)) == P(next)", "Holds(P(_)) == TRUE"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla Holds");
});

test("TLA+ definitions with nested brackets or a leading digit are their own recorded definitions", () => {
  const named = (files) => {
    edit(files.spec, "InWindow == consumed <= next /\\ next <= consumed + Window", "InWindow == consumed <= next /\\ next <= 1aBound /\\ Pair[[a |-> 0]] = 0");
    edit(files.spec, "\nSpec ==", "\n1aBound == consumed + Window\nPair[r \\in [a : {0, 1}]] == r.a\n\nSpec ==");
  };
  assertChanged(recordedThenEdited(named, "matrix", tla("1aBound == consumed + Window", "1aBound == consumed + Window + 1")), "matrix", "changed definition BoundedQueue.tla 1aBound");
  assertChanged(recordedThenEdited(named, "matrix", tla("== r.a", "== 0")), "matrix", "changed definition BoundedQueue.tla Pair");
});

test("a column-0 TLA+ definition the record cannot name is recorded whether or not a property names it", () => {
  const infix = (files) => edit(files.spec, "\nSpec ==", "\na \\prec b == a < b\n\nSpec ==");
  assertChanged(recordedThenEdited(infix, "matrix", tla("a \\prec b == a < b", "a \\prec b == a <= b")), "matrix", "changed definition BoundedQueue.tla a \\prec b");
  const local = tla("InWindow == consumed <= next /\\ next <= consumed + Window", "InWindow ==\nLET d == consumed + Window IN\nconsumed <= next /\\ next <= d");
  assertChanged(recordedThenEdited(local, "matrix", tla("consumed + Window IN", "consumed + Window + 1 IN")), "matrix", "changed definition BoundedQueue.tla LET d");
});

test("a TLA+ comment edit and an added run line leave the model unchanged", () => {
  assertUnchanged(recordedThenEdited(null, "matrix", tla("\\* Stutter at the end", "\\* Stutters at the very end")), "matrix");
  assertUnchanged(recordedThenEdited(null, "matrix", tla("consumed <= next /\\", "consumed <=   next (* why *) /\\")), "matrix");
  assertUnchanged(recordedThenEdited(null, "matrix", ({ matrix }) => edit(matrix, "run window=4 items=0 | Window=4 Items=0", "run window=4 items=0 | Window=4 Items=0\nrun window=2 items=2 | Window=2 Items=2")), "matrix");
});

test("TLA+ comment markers inside strings do not hide changes to a property", () => {
  for (const literal of [String.raw`"(*"`, String.raw`"\\*"`, String.raw`"\"(*"`]) {
    const property = `AllConsumed == <>(consumed = Items) /\\ ${literal} # "bad"`;
    const setup = tla("AllConsumed == <>(consumed = Items)", property);
    assertChanged(recordedThenEdited(setup, "matrix", tla(' # "bad"', ' # "worse"')), "matrix", "changed definition BoundedQueue.tla AllConsumed");
  }
});

test("whitespace inside TLA+ string literals is part of the property", () => {
  const setup = tla("AllConsumed == <>(consumed = Items)", 'AllConsumed == <>(consumed = Items) /\\ "a b" # "a  b"');
  assertChanged(recordedThenEdited(setup, "matrix", tla('"a  b"', '"a b"')), "matrix", "changed definition BoundedQueue.tla AllConsumed");
});

test("a TLA+ run whose constants change is changed", () => {
  const outcome = recordedThenEdited(null, "matrix", ({ matrix }) => edit(matrix, "Window=4 Items=5", "Window=4 Items=1"));
  assertChanged(outcome, "matrix", "changed run BoundedQueue.tla window=4 items=5");
});

test("a TLA+ property that names a missing operator fails", () => {
  const files = models();
  edit(files.matrix, "check PROPERTIES AllConsumed", "check PROPERTIES NoSuchProperty");
  const result = baseline(files.dir, "record", files.record, files.matrix);
  assert.equal(result.status, 1);
  assert.ok(lines(result)[0].startsWith("FAIL baseline:"));
  assert.ok(result.stdout.includes("NoSuchProperty"));
});

test("a malformed matrix line fails the record", () => {
  const files = models();
  edit(files.matrix, "reach WindowFull | window=1", "reach WindowFull");
  const result = baseline(files.dir, "record", files.record, files.matrix);
  assert.equal(result.status, 1);
  assert.ok(result.stdout.includes("malformed reach"));
});

test("an added Kani assume is changed", () => {
  const outcome = recordedThenEdited(null, "rust", rust("kani::assume(window > 0 && window <= 2);", "kani::assume(window > 0 && window <= 2);\n        kani::assume(state.next == 0);"));
  assertChanged(outcome, "rust", "added assume state.next == 0");
});

test("moving a Kani assumption from a helper into a harness changes its owner", () => {
  const outcome = recordedThenEdited(null, "rust", ({ rust: path }) => {
    edit(path, "        kani::assume(window > 0 && window <= 2);\n", "");
    edit(path, "        let (window, state) = inputs();", "        let (window, state) = inputs();\n        kani::assume(window > 0 && window <= 2);");
  });
  assertChanged(outcome, "rust", "removed assume window > 0 && window <= 2", "added assume window > 0 && window <= 2");
});

test("Kani items retain qualified owners when equal function names occur in nested modules", () => {
  const setup = ({ rust: path }) => writeFileSync(path, [
    "mod outer { mod a { #[kani::proof] fn same() { kani::assume(true); } }",
    "mod b { #[kani::proof] fn same() {} } }", "",
  ].join("\n"));
  const outcome = recordedThenEdited(setup, "rust", ({ rust: path }) => {
    edit(path, "fn same() { kani::assume(true); }", "fn same() {}");
    edit(path, "mod b { #[kani::proof] fn same() {}", "mod b { #[kani::proof] fn same() { kani::assume(true); }");
  });
  assertChanged(outcome, "rust", "removed assume true in outer::a::same", "added assume true in outer::b::same");
});

test("moving a Kani cover or stub between functions changes its owner", () => {
  for (const [first, second, kind] of [
    ["fn a() { kani::cover!(true); } fn b() {}", "fn a() {} fn b() { kani::cover!(true); }", "cover true"],
    ["#[kani::stub(real, fake)] fn a() {} fn b() {}", "fn a() {} #[kani::stub(real, fake)] fn b() {}", "stub real, fake"],
  ]) {
    const setup = ({ rust: path }) => writeFileSync(path, first);
    const outcome = recordedThenEdited(setup, "rust", ({ rust: path }) => writeFileSync(path, second));
    assertChanged(outcome, "rust", `removed ${kind} in a`);
  }
});

test("reordering functions with identical Kani assumptions preserves their owners", () => {
  const a = "fn a() { kani::assume(true); kani::assume(true); }";
  const b = "fn b() { kani::assume(true); }";
  const setup = ({ rust: path }) => writeFileSync(path, `${a}\n${b}\n`);
  assertUnchanged(recordedThenEdited(setup, "rust", ({ rust: path }) => writeFileSync(path, `${b}\n${a}\n`)), "rust");
  const removed = recordedThenEdited(setup, "rust", ({ rust: path }) => edit(path, a, "fn a() { kani::assume(true); }"));
  assertChanged(removed, "rust", "removed assume true in a #2");
});

test("conditional definitions with the same qualified name retain separate Kani owners", () => {
  const setup = ({ rust: path }) => writeFileSync(path, "#[cfg(a)] fn same() { kani::assume(true); } #[cfg(b)] fn same() {}");
  const outcome = recordedThenEdited(setup, "rust", ({ rust: path }) => {
    edit(path, "{ kani::assume(true); }", "{}");
    edit(path, "#[cfg(b)] fn same() {}", "#[cfg(b)] fn same() { kani::assume(true); }");
  });
  assertChanged(outcome, "rust", "removed assume true in same", "added assume true in same[2]");
});

test("duplicate assumptions cannot stand in for a constraint on a different function definition", () => {
  const setup = ({ rust: path }) => writeFileSync(path,
    "#[cfg(a)] fn same() { kani::assume(true); kani::assume(true); } #[cfg(b)] fn same() { kani::assume(true); }");
  const outcome = recordedThenEdited(setup, "rust", ({ rust: path }) => writeFileSync(path,
    "#[cfg(a)] fn same() { kani::assume(true); } #[cfg(b)] fn same() { kani::assume(true); kani::assume(true); }"));
  assertChanged(outcome, "rust", "added assume true in same");
});

test("generic free functions and local blocks retain their Kani owner", () => {
  const setup = ({ rust: path }) => writeFileSync(path, "mod m { pub unsafe fn r#type<'a, const N: usize>(x: &'a [u8; N]) { if N > 0 { kani::assume(x[0] > 0); } } }");
  const outcome = recordedThenEdited(setup, "rust", ({ rust: path }) => edit(path, "x[0] > 0", "x[0] > 1"));
  assertChanged(outcome, "rust", "removed assume x[0] > 0 in m::r#type");
});

test("a Kani form in an unsupported Rust owner fails instead of being recorded without context", () => {
  for (const source of [
    "impl State { fn helper() { kani::assume(true); } }",
    "trait T { fn helper() { kani::assume(true); } }",
    "macro_rules! body { () => { kani::assume(true); } }",
    "fn helper() { wrapper! { kani::assume(true); } }",
    "fn helper() { wrapper!(kani::assume(true)); }",
    "fn helper() { macro_rules! body { () => { kani::assume(true); } } }",
    "fn helper() { impl State { fn local() { kani::assume(true); } } }",
    "kani::assume(true);",
  ]) {
    const files = models();
    writeFileSync(files.rust, source);
    const result = baseline(files.dir, "record", files.record, files.rust);
    assert.equal(result.status, 1, source);
    assert.ok(result.stdout.includes("cannot identify a function owner"), result.stdout);
  }
});

const multiline = rust("kani::assume(window > 0 && window <= 2);", "kani::assume(\n            window > 0\n            && window <= 2,\n        );");

test("an edit to one line of a multi-line Kani assume is changed", () => {
  const outcome = recordedThenEdited(multiline, "rust", rust("&& window <= 2,", "&& window <= 3,"));
  assertChanged(outcome, "rust", "removed assume window > 0 && window <= 2,", "added assume window > 0 && window <= 3,");
});

test("a reformatted Kani assume is unchanged", () => {
  assertUnchanged(recordedThenEdited(multiline, "rust", rust("window > 0\n            && window <= 2,", "window > 0 && window <= 2,")), "rust");
});

test("whitespace inside Rust string literals is part of a Kani assumption", () => {
  for (const literal of ['"a b"', 'b"a b"', 'r##"a b"##', 'br#"a b"#', String.raw`r#"a \" b"#`, 'cr#"a " b " c"#']) {
    const value = literal.startsWith("cr") ? `${literal}.to_bytes()` : literal;
    const assumption = `kani::assume(${value}.len() == usize::from(window));`;
    const setup = rust("kani::assume(window > 0 && window <= 2);", assumption);
    assertChanged(recordedThenEdited(setup, "rust", rust(literal, literal.replace(" b", "  b"))), "rust", "removed assume", "added assume");
    assertUnchanged(recordedThenEdited(setup, "rust", rust(assumption, `kani::assume(\n    ${value}.len() == usize::from(window)\n);`)), "rust");
  }
});

test("a removed Kani cover is changed and an added cover is not", () => {
  assertChanged(recordedThenEdited(null, "rust", rust('        kani::cover!(state.next == state.consumed, "queue empty");\n', "")), "rust", 'removed cover state.next == state.consumed, "queue empty"');
  assertUnchanged(recordedThenEdited(null, "rust", rust("        if let Some(after) = consume(state) {", '        kani::cover!(state.next == 3, "three");\n        if let Some(after) = consume(state) {')), "rust");
});

test("a removed Kani harness is changed", () => {
  const remove = rust("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn consume_keeps_invariant", "    #[kani::unwind(2)]\n    fn consume_keeps_invariant");
  assertChanged(recordedThenEdited(null, "rust", remove), "rust", "removed harness proofs::consume_keeps_invariant");
});

test("a Kani body edit that touches no assume, cover, stub or harness is unchanged", () => {
  assertUnchanged(recordedThenEdited(null, "rust", rust("Some(State { next: state.next + 1, ..state })", "Some(State { next: state.next + 2, ..state })")), "rust");
  const commented = rust("kani::assume(invariant(window, state));", '// kani::assume(false);\n        let _text = "kani::assume(false)";\n        kani::assume(invariant(window, state));');
  assertUnchanged(recordedThenEdited(null, "rust", commented), "rust");
});

test("an added Kani stub is changed", () => {
  const outcome = recordedThenEdited(null, "rust", rust("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant", "    #[kani::proof]\n    #[kani::stub(consume, claim)]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant"));
  assertChanged(outcome, "rust", "added stub consume, claim");
});

test("an added kani::any_where narrows like an assume and is changed", () => {
  const outcome = recordedThenEdited(null, "rust", rust("let window: u16 = kani::any();", "let window: u16 = kani::any_where(|w: &u16| *w == 1);"));
  assertChanged(outcome, "rust", "added assume |w: &u16| *w == 1");
});

test("a harness and stub written under cfg_attr(kani, ...) are recorded", () => {
  const wrapped = rust("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant", "    #[cfg_attr(kani, kani::proof)]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant");
  const removed = recordedThenEdited(wrapped, "rust", rust("    #[cfg_attr(kani, kani::proof)]\n", ""));
  assertChanged(removed, "rust", "removed harness proofs::claim_keeps_invariant");
  const stubbed = recordedThenEdited(null, "rust", rust("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant", "    #[kani::proof]\n    #[cfg_attr(kani, kani::stub(consume, claim))]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant"));
  assertChanged(stubbed, "rust", "added stub consume, claim");
});

test("an any_where with a nested turbofish is read as an assume", () => {
  const outcome = recordedThenEdited(null, "rust", rust("let window: u16 = kani::any();", "let window: u16 = kani::any_where::<Option<u16>>(|w| w.is_some()).unwrap();"));
  assertChanged(outcome, "rust", "added assume |w| w.is_some()");
});

test("a Kani path under another crate and a precise capture record", () => {
  const files = models();
  edit(files.rust, "#[cfg(kani)]", "use crate::kani::helpers::proof_state;\nfn keep<'a>(x: &'a u8) -> impl Sized + use<'a> { x }\n#[cfg(kani)]");
  assert.equal(baseline(files.dir, "record", files.record, files.rust).status, 0);
});

test("a Kani form or import the record cannot read fails the record instead of passing unrecorded", () => {
  const forms = [
    ["#[cfg(kani)]", "use kani::assume;\n#[cfg(kani)]", "use kani::assume"],
    ["#[cfg(kani)]", "use ::kani::{any, assume as given};\n#[cfg(kani)]", "use ::kani::{any, assume"],
    ["#[cfg(kani)]", "extern crate kani as k;\n#[cfg(kani)]", "extern crate kani as"],
    ["#[cfg(kani)]", "use {kani as k};\n#[cfg(kani)]", "use {kani as"],
    ["    #[kani::unwind(2)]\n    fn claim_keeps_invariant", "    #[cfg_attr(all(kani, test), kani::stub(consume, claim))]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant", "kani::stub"],
  ];
  for (const [from, to, named] of forms) {
    const files = models();
    edit(files.rust, from, to);
    const result = baseline(files.dir, "record", files.record, files.rust);
    assert.equal(result.status, 1, to);
    assert.ok(lines(result)[0].startsWith("FAIL baseline:"), result.stdout);
    assert.ok(result.stdout.includes(named), result.stdout);
  }
});

test("re-recording a changed file prints the previous digest, and compare then passes", () => {
  const files = models();
  const first = baseline(files.dir, "record", files.record, files.rust);
  const digest = lines(first)[0].split(" ").at(-1);
  edit(files.rust, "kani::assume(window > 0 && window <= 2);", "kani::assume(window > 0 && window <= 1);");
  const second = lines(baseline(files.dir, "record", files.record, files.rust));
  assert.ok(second[0].startsWith(`RECORDED ${files.rust} `));
  assert.equal(second[1], `  previous ${digest}`);
  assert.equal(baseline(files.dir, "compare", files.record).status, 0);
});

test("recording one file keeps the other entries, and a repeat record prints no previous digest", () => {
  const files = models();
  baseline(files.dir, "record", files.record, files.rust);
  const again = baseline(files.dir, "record", files.record, files.rust);
  assert.equal(lines(again).length, 1);
  baseline(files.dir, "record", files.record, files.matrix, files.statements);
  const result = baseline(files.dir, "compare", files.record);
  assert.equal(result.status, 0);
  assert.equal(lines(result).at(-1), "SUMMARY 3 unchanged, 0 changed");
});

test("a deleted model file is changed", () => {
  assertChanged(recordedThenEdited(null, "rust", ({ rust: path }) => rmSync(path)), "rust", "file is missing");
});

test("a malformed record fails", () => {
  const files = models();
  writeFileSync(files.record, "{}\n");
  const result = baseline(files.dir, "compare", files.record);
  assert.equal(result.status, 1);
  assert.ok(lines(result)[0].startsWith("FAIL baseline:"));
});

test("records without execution context are rejected rather than compared as current records", () => {
  const files = models();
  writeFileSync(files.record, JSON.stringify({ format: 1, models: {} }));
  const result = baseline(files.dir, "compare", files.record);
  assert.equal(result.status, 1);
  assert.ok(result.stdout.includes("unsupported record format"));
});

test("an unknown extension and a missing record file are usage errors", () => {
  const files = models();
  writeFileSync(join(files.dir, "notes.txt"), "text\n");
  const unknown = baseline(files.dir, "record", files.record, join(files.dir, "notes.txt"));
  assert.equal(unknown.status, 2);
  assert.ok(unknown.stdout.includes("notes.txt"));
  const missing = baseline(files.dir, "compare", files.record);
  assert.equal(missing.status, 2);
  assert.ok(missing.stdout.includes("does not exist"));
  assert.equal(baseline(files.dir, "frobnicate").status, 2);
});
