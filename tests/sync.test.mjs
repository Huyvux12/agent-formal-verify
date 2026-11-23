// Copyright (c) 2026 Michael Denyer
// SPDX-License-Identifier: GPL-3.0-only
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { afterEach, test } from "node:test";
import { fixture, removeFixtures, scripts } from "./helpers.mjs";

afterEach(removeFixtures);

// Git sets GIT_DIR and GIT_INDEX_FILE for a hook such as pre-commit, which runs these tests. Left in place, they
// would point every git command here at the repository being committed to. The developer's git configuration,
// such as commit signing, stays out of the fixture repositories too.
const gitEnv = {
  ...Object.fromEntries(Object.entries(process.env).filter(([name]) => !name.startsWith("GIT_"))),
  GIT_CONFIG_GLOBAL: "/dev/null",
  GIT_CONFIG_NOSYSTEM: "1",
  GIT_AUTHOR_NAME: "Test",
  GIT_AUTHOR_EMAIL: "test@example.invalid",
  GIT_COMMITTER_NAME: "Test",
  GIT_COMMITTER_EMAIL: "test@example.invalid",
};

function git(dir, ...args) {
  const result = spawnSync("git", ["-C", dir, ...args], { encoding: "utf8", env: gitEnv });
  assert.equal(result.status, 0, result.stderr);
  return result.stdout.trim();
}

function commit(dir, files, message) {
  for (const [path, text] of Object.entries(files)) {
    mkdirSync(join(dir, path, ".."), { recursive: true });
    writeFileSync(join(dir, path), text);
  }
  git(dir, "add", "-A");
  git(dir, "commit", "-m", message);
  return git(dir, "rev-parse", "HEAD");
}

function sync(dir, args, cwd = dir) {
  return spawnSync("python3", [join(scripts, "sync.py"), ...args], { cwd, encoding: "utf8", env: gitEnv });
}

function lines(output, tag) {
  return output.split("\n").filter((line) => line.startsWith(tag + " "));
}

test("sync follows renames, finds where covered names live now, and names the commit that removed one", () => {
  const dir = fixture();
  git(dir, "init", "-b", "main");
  const read = commit(dir, { "src/queue.c": "int claim(void);\nint consume(void);\nint drain(void);\n" }, "queue");
  commit(dir, { "tla/Queue.tla": `(* Source read at ${read} *)\nclaim consume drain\n` }, "model");
  git(dir, "mv", "src/queue.c", "src/core.c");
  git(dir, "commit", "-m", "rename");
  commit(dir, { "src/core.c": "int claim(void);\nint drain(void);\n", "src/consume.c": "int consume(void);\n" }, "move consume");
  commit(dir, { "src/core.c": "int claim(void);\n" }, "remove drain");
  const removed = git(dir, "rev-parse", "--short", "HEAD");

  const result = sync(dir, ["tla/Queue.tla", "--source", "src/queue.c", "--name", "claim", "--name", "consume", "--name", "drain"]);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(lines(result.stdout, "SYNC"), [`SYNC ${read} from the Source read at line in Queue.tla`]);
  assert.deepEqual(lines(result.stdout, "PATH"), ["PATH src/consume.c", "PATH src/core.c", "PATH src/queue.c"]);
  assert.deepEqual(lines(result.stdout, "MISSING"), [`MISSING drain: ${removed}`]);
  const root = git(dir, "rev-parse", "--show-toplevel");
  assert.deepEqual(lines(result.stdout, "READ"), [`READ git -C ${root} log -p ${read}..HEAD -- src/consume.c src/core.c src/queue.c`]);
});

test("sync falls back to the last commit of the model files when the header's commit is not in HEAD's history", () => {
  const dir = fixture();
  git(dir, "init", "-b", "main");
  commit(dir, { "src/queue.c": "int claim(void);\n" }, "queue");
  const model = commit(dir, { "tla/Queue.tla": "(* Source read at 0123456789abcdef0123456789abcdef01234567 *)\n" }, "model");
  const result = sync(dir, ["tla/Queue.tla", "--source", "src/queue.c"]);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(lines(result.stdout, "SYNC"), [
    `SYNC ${model} from the last commit of the model files; the Source read at commit 0123456789abcdef0123456789abcdef01234567 in Queue.tla is not in HEAD's history`,
  ]);
  assert.deepEqual(lines(result.stdout, "PATH"), ["PATH src/queue.c"]);

  const quoted = commit(dir, { "tla/Queue.tla": "(* Source read at `abc1234` *)\n" }, "quoted");
  const off = sync(dir, ["tla/Queue.tla"]);
  assert.equal(off.status, 0, off.stdout + off.stderr);
  assert.equal(off.stdout, `SYNC ${quoted} from the last commit of the model files; the Source read at line in Queue.tla names no commit hash\n`);
});

test("sync reports a model with no sync commit, and searches a model file only when it is also a source", () => {
  const dir = fixture();
  git(dir, "init", "-b", "main");
  commit(dir, { "src/lib.rs": "pub fn claim() {}\n" }, "start");
  commit(dir, { "tla/Queue.tla": "claim\n" }, "model");
  writeFileSync(join(dir, "tla/New.tla"), "claim\n");
  const none = sync(dir, ["tla/New.tla", "--name", "claim"]);
  assert.equal(none.status, 0, none.stdout + none.stderr);
  assert.equal(none.stdout, "SYNC none: the model files have no commit and no Source read at line in HEAD's history; compare the model with the code in full\n");

  const rust = sync(dir, ["src/lib.rs", "tla/Queue.tla", "--source", "src/lib.rs", "--name", "claim"]);
  assert.equal(rust.status, 0, rust.stdout + rust.stderr);
  assert.deepEqual(lines(rust.stdout, "PATH"), ["PATH src/lib.rs"]);
});

test("sync falls back past production edits to a model file that is also a source", () => {
  const dir = fixture();
  git(dir, "init", "-b", "main");
  const proofs = "\n// Harnesses for claim.\n#[cfg(kani)]\nmod proofs {\n    #[kani::proof]\n    fn check() { assert!(super::claim() == 1); }\n}\n";
  commit(dir, { "src/lib.rs": "pub fn claim() -> u8 { 1 }\n" }, "production");
  const harness = commit(dir, { "src/lib.rs": "pub fn claim() -> u8 { 1 }\n" + proofs }, "harness");
  commit(dir, { "src/lib.rs": "pub fn claim() -> u8 { 2 }\n" + proofs }, "production edit");
  commit(dir, { "src/lib.rs": "// Returns the next slot.\npub fn claim() -> u8 { 2 }\n" + proofs }, "comment");

  const result = sync(dir, ["src/lib.rs", "--source", "src/lib.rs", "--name", "claim"]);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(lines(result.stdout, "SYNC"), [`SYNC ${harness} from the last commit of the model files that changed no production code in lib.rs`]);
  const root = git(dir, "rev-parse", "--show-toplevel");
  assert.deepEqual(lines(result.stdout, "READ"), [`READ git -C ${root} log -p ${harness}..HEAD -- src/lib.rs`]);

  // A commit that changed another model file together with the production code is not one either.
  commit(dir, { "src/lib.rs": "pub fn claim() -> u8 { 3 }\n" + proofs, "tla/Queue.tla": "claim\n" }, "model and production");
  const mixed = sync(dir, ["src/lib.rs", "tla/Queue.tla", "--source", "src/lib.rs"]);
  assert.equal(mixed.status, 0, mixed.stdout + mixed.stderr);
  assert.deepEqual(lines(mixed.stdout, "SYNC"), [`SYNC ${harness} from the last commit of the model files that changed no production code in lib.rs`]);

  // The harness came with the production code, so no commit changed the harness alone.
  const fresh = fixture();
  git(fresh, "init", "-b", "main");
  commit(fresh, { "src/lib.rs": "pub fn claim() -> u8 { 1 }\n" + proofs }, "production and harness");
  commit(fresh, { "src/lib.rs": "pub fn claim() -> u8 { 2 }\n" + proofs }, "production edit");
  const none = sync(fresh, ["src/lib.rs", "--source", "src/lib.rs", "--name", "claim"]);
  assert.equal(none.status, 0, none.stdout + none.stderr);
  assert.equal(none.stdout, "SYNC none: no commit of the model files changed only the #[cfg(kani)] items of lib.rs; compare the model with the code in full\n");
});

test("sync's fallback counts #[cfg(kani)] on an item only, and says when it stops at a rename or after the last 100 commits", () => {
  const dir = fixture();
  git(dir, "init", "-b", "main");
  const proofs = "\n#[cfg(kani)]\nmod proofs {\n    #[kani::proof]\n    fn check() { assert!(super::claim() == 1); }\n}\n";
  const event = "pub enum Event {\n    #[cfg(kani)]\n    Ghost,\n    Release,\n}\n";
  commit(dir, { "src/lib.rs": event + "pub fn claim() -> u8 { 1 }\n" }, "production");
  const harness = commit(dir, { "src/lib.rs": event + "pub fn claim() -> u8 { 1 }\n" + proofs }, "harness");
  commit(dir, { "src/lib.rs": event + "pub fn claim() -> u8 { 2 }\n" + proofs }, "production edit");
  const variant = sync(dir, ["src/lib.rs", "--source", "src/lib.rs"]);
  assert.equal(variant.status, 0, variant.stdout + variant.stderr);
  assert.deepEqual(lines(variant.stdout, "SYNC"), [`SYNC ${harness} from the last commit of the model files that changed no production code in lib.rs`]);

  git(dir, "mv", "src/lib.rs", "src/core.rs");
  git(dir, "commit", "-m", "rename");
  const moved = git(dir, "rev-parse", "HEAD");
  commit(dir, { "src/core.rs": event + "pub fn claim() -> u8 { 3 }\n" + proofs }, "production edit after the rename");
  const renamed = sync(dir, ["src/core.rs", "--source", "src/core.rs"]);
  assert.equal(renamed.status, 0, renamed.stdout + renamed.stderr);
  assert.equal(
    renamed.stdout,
    `SYNC none: no commit of the model files changed only the #[cfg(kani)] items of core.rs since the rename to core.rs in ${moved}, which git log does not follow; compare the model with the code in full\n`,
  );

  for (let edit = 4; edit < 105; edit++) {
    writeFileSync(join(dir, "src/core.rs"), event + `pub fn claim() -> u8 { ${edit} }\n` + proofs);
    git(dir, "commit", "-am", `edit ${edit}`);
  }
  const long = sync(dir, ["src/core.rs", "--source", "src/core.rs"]);
  assert.equal(long.status, 0, long.stdout + long.stderr);
  assert.equal(long.stdout, "SYNC none: no commit of the last 100 commits of the model files changed only the #[cfg(kani)] items of core.rs; compare the model with the code in full\n");
});

test("sync leaves a model file out of the name search when it is not also a source", () => {
  const dir = fixture();
  git(dir, "init", "-b", "main");
  // The harness in its own file still calls a function that the production code no longer has.
  commit(dir, { "src/lib.rs": "pub fn claim() {}\n", "verify/src/harness.rs": "fn check() { claim(); drain(); }\n" }, "start");
  const harness = sync(dir, ["verify/src/harness.rs", "--name", "claim", "--name", "drain"]);
  assert.equal(harness.status, 0, harness.stdout + harness.stderr);
  assert.deepEqual(lines(harness.stdout, "PATH"), ["PATH src/lib.rs"]);
  assert.deepEqual(lines(harness.stdout, "MISSING"), ["MISSING drain: no commit since the sync removed it"]);
});

test("sync follows a rename between non-ASCII paths and searches for a name as a fixed string", () => {
  const dir = fixture();
  git(dir, "init", "-b", "main");
  const read = commit(dir, { "src/café.cpp": "int operator[](int);\n" }, "queue");
  commit(dir, { "tla/Queue.tla": `(* Source read at ${read} *)\n` }, "model");
  git(dir, "mv", "src/café.cpp", "src/naïve.cpp");
  git(dir, "commit", "-m", "rename");
  const result = sync(dir, ["tla/Queue.tla", "--source", "src/café.cpp", "--name", "operator[]"]);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(lines(result.stdout, "PATH"), ["PATH src/café.cpp", "PATH src/naïve.cpp"]);
  assert.deepEqual(lines(result.stdout, "MISSING"), []);
});

test("sync fails for a source path that no commit has", () => {
  const dir = fixture();
  git(dir, "init", "-b", "main");
  commit(dir, { "src/queue.c": "int claim(void);\n", "tla/Queue.tla": "claim\n" }, "start");
  const result = sync(dir, ["../tla/Queue.tla", "--source", "src/queue.c"], join(dir, "src"));
  assert.equal(result.status, 1);
  assert.match(result.stdout, /^SYNC [0-9a-f]{40} from the last commit of the model files\nFAIL --source src\/queue\.c is .*src\/src\/queue\.c, which no commit in .* has\n$/);
});

test("sync fails outside a git repository", () => {
  const dir = fixture();
  writeFileSync(join(dir, "Queue.tla"), "\n");
  const result = sync(dir, ["Queue.tla"]);
  assert.equal(result.status, 1);
  assert.match(result.stdout, /^FAIL .*Queue\.tla is in no git repository\n$/);
});
