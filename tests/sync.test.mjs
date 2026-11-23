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

function sync(dir, args) {
  return spawnSync("python3", [join(scripts, "sync.py"), ...args], { cwd: dir, encoding: "utf8", env: gitEnv });
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
  assert.deepEqual(lines(result.stdout, "SYNC"), [`SYNC ${model} from the last commit of the model files`]);
  assert.deepEqual(lines(result.stdout, "PATH"), ["PATH src/queue.c"]);
});

test("sync reports a model with no sync commit, and keeps a Rust model file in the name search", () => {
  const dir = fixture();
  git(dir, "init", "-b", "main");
  commit(dir, { "src/lib.rs": "pub fn claim() {}\n", "tla/Queue.tla": "claim\n" }, "start");
  writeFileSync(join(dir, "tla/New.tla"), "claim\n");
  const none = sync(dir, ["tla/New.tla", "--name", "claim"]);
  assert.equal(none.status, 0, none.stdout + none.stderr);
  assert.equal(none.stdout, "SYNC none: the model files have no commit and no Source read at line in HEAD's history; compare the model with the code in full\n");

  const rust = sync(dir, ["src/lib.rs", "tla/Queue.tla", "--name", "claim"]);
  assert.equal(rust.status, 0, rust.stdout + rust.stderr);
  assert.deepEqual(lines(rust.stdout, "PATH"), ["PATH src/lib.rs"]);
});

test("sync fails outside a git repository", () => {
  const dir = fixture();
  writeFileSync(join(dir, "Queue.tla"), "\n");
  const result = sync(dir, ["Queue.tla"]);
  assert.equal(result.status, 1);
  assert.match(result.stdout, /^FAIL .*Queue\.tla is in no git repository\n$/);
});
