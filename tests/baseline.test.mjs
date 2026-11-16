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

test("a TLA+ Spec that loses fairness is changed", () => {
  assertChanged(recordedThenEdited(null, "matrix", tla(" /\\ WF_vars(Consume)", "")), "matrix", "changed definition BoundedQueue.tla Spec");
});

test("a weakened TLA+ property is changed", () => {
  const outcome = recordedThenEdited(null, "matrix", tla("next <= consumed + Window", "next <= consumed + Window + 1"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla InWindow");
});

test("a TLA+ helper that a property references is changed, and an action that none references is not", () => {
  const helper = (files) => {
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "Finished == consumed = Items\nAllConsumed == <>Finished");
  };
  const outcome = recordedThenEdited(helper, "matrix", tla("Finished == consumed = Items", "Finished == consumed >= 0"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla Finished");
  assertUnchanged(recordedThenEdited(null, "matrix", tla("next' = next + 1", "next' = next + 2")), "matrix");
});

test("a TLA+ comment edit and an added run line leave the model unchanged", () => {
  assertUnchanged(recordedThenEdited(null, "matrix", tla("\\* Stutter at the end", "\\* Stutters at the very end")), "matrix");
  assertUnchanged(recordedThenEdited(null, "matrix", tla("consumed <= next /\\", "consumed <=   next (* why *) /\\")), "matrix");
  const run = recordedThenEdited(null, "matrix", ({ matrix }) => edit(matrix, "run window=4 items=0 | Window=4 Items=0", "run window=4 items=0 | Window=4 Items=0\nrun window=2 items=2 | Window=2 Items=2"));
  assertUnchanged(run, "matrix");
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

const multiline = (files) => edit(files.rust, "kani::assume(window > 0 && window <= 2);", "kani::assume(\n            window > 0\n            && window <= 2,\n        );");

test("an edit to one line of a multi-line Kani assume is changed", () => {
  const outcome = recordedThenEdited(multiline, "rust", rust("&& window <= 2,", "&& window <= 3,"));
  assertChanged(outcome, "rust", "removed assume window > 0 && window <= 2,", "added assume window > 0 && window <= 3,");
});

test("a reformatted Kani assume is unchanged", () => {
  assertUnchanged(recordedThenEdited(multiline, "rust", rust("window > 0\n            && window <= 2,", "window > 0 && window <= 2,")), "rust");
});

test("a removed Kani cover is changed and an added cover is not", () => {
  assertChanged(recordedThenEdited(null, "rust", rust('        kani::cover!(state.next == state.consumed, "queue empty");\n', "")), "rust", 'removed cover state.next == state.consumed, "queue empty"');
  assertUnchanged(recordedThenEdited(null, "rust", rust("        if let Some(after) = consume(state) {", '        kani::cover!(state.next == 3, "three");\n        if let Some(after) = consume(state) {')), "rust");
});

test("a removed Kani harness is changed", () => {
  const remove = ({ rust: path }) => {
    const text = readFileSync(path, "utf8");
    writeFileSync(path, text.replace("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn consume_keeps_invariant", "    #[kani::unwind(2)]\n    fn consume_keeps_invariant"));
  };
  assertChanged(recordedThenEdited(null, "rust", remove), "rust", "removed harness consume_keeps_invariant");
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

test("re-recording a changed file prints the previous digest, and compare then passes", () => {
  const files = models();
  const first = baseline(files.dir, "record", files.record, files.rust);
  const digest = lines(first)[0].split(" ").at(-1);
  edit(files.rust, "kani::assume(window > 0 && window <= 2);", "kani::assume(window > 0 && window <= 1);");
  const second = lines(baseline(files.dir, "record", files.record, files.rust));
  assert.equal(second[0].startsWith(`RECORDED ${files.rust} `), true);
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
