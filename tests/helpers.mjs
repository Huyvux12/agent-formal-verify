// Copyright (c) 2026 Michael Denyer
// SPDX-License-Identifier: GPL-3.0-only
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { chmodSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

// Every test file imports this module, so each helper a test starts sees its own settings at their defaults
// unless the test sets them, whatever the developer's shell exports.
delete process.env.TLC_TIMEOUT;
delete process.env.TLC_WORKERS;
delete process.env.TLC_CACHE;
delete process.env.KANI_HARNESS_TIMEOUT;
delete process.env.FORMAL_MIN_FREE_GIB;

export const root = fileURLToPath(new URL("..", import.meta.url));
export const scripts = join(root, "skills/formal-verify/scripts");
export const logs = join(root, "tests/fixtures");
export const includes = (text, part) => assert.ok(text.includes(part), `${JSON.stringify(text)} lacks ${JSON.stringify(part)}`);
export const excludes = (text, part) => assert.ok(!text.includes(part), `${JSON.stringify(text)} has ${JSON.stringify(part)}`);

const fixtures = [];
export function removeFixtures() {
  for (const dir of fixtures.splice(0)) rmSync(dir, { recursive: true, force: true });
}
// Leave a fixture in place after the test, for a failure that needs its files to diagnose.
export function keepFixture(dir) {
  fixtures.splice(fixtures.indexOf(dir) >>> 0, 1);
}
export function fixture() {
  const dir = mkdtempSync(join(tmpdir(), "formal-tools-"));
  fixtures.push(dir);
  mkdirSync(join(dir, "bin"));
  return dir;
}
export function command(dir, name, body) {
  const path = join(dir, "bin", name);
  writeFileSync(path, "#!/bin/bash\n" + body + "\n");
  chmodSync(path, 0o755);
  return path;
}
export function fakeTlc(dir, body) {
  return command(dir, "tlc-java", '[[ "$*" == *"-help"* ]] && exit 0\n[ "$1" = "-version" ] && exit 0\n' + body);
}
export const leanPin = "leanprover/lean4:v4.34.1";
export function writeLeanProject(project) {
  mkdirSync(project, { recursive: true });
  writeFileSync(join(project, "lakefile.toml"), 'name = "model"\n');
  writeFileSync(join(project, "lean-toolchain"), leanPin + "\n");
}
export function run(dir, script, args = [], extra = {}) {
  return spawnSync(script.endsWith(".py") ? "python3" : "bash", [join(scripts, script), ...args], {
    encoding: "utf8",
    env: {
      ...process.env,
      PATH: join(dir, "bin") + ":" + process.env.PATH,
      JAVA: command(dir, "java", "exit 0"),
      TLC_JAR: "",
      TASK_TRACE: join(dir, "calls"),
      ...extra,
    },
  });
}

export function isStopped(pid) {
  try {
    process.kill(pid, 0);
  } catch (error) {
    return error.code === "ESRCH";
  }
  try {
    const stat = readFileSync(`/proc/${pid}/stat`, "utf8");
    const afterName = stat.slice(stat.lastIndexOf(") ") + 2);
    if (afterName.startsWith("Z")) return true;
  } catch {
    // Non-Linux hosts have no /proc/<pid>/stat; fall back to ps below.
  }
  const ps = spawnSync("ps", ["-o", "stat=", "-p", String(pid)], { encoding: "utf8" });
  return !ps.error && ps.status === 0 && (ps.stdout.trim() === "" || ps.stdout.trim().startsWith("Z"));
}

export function processesWhere(match) {
  const listing = spawnSync("ps", ["-A", "-ww", "-o", "pid=,command="], { encoding: "utf8" }).stdout;
  return listing.split("\n").map((line) => line.trim().split(/\s+/)).filter(([pid, ...command]) => pid && match(command.join(" "))).map(([pid]) => Number(pid));
}

export function waitFor(condition) {
  const deadline = Date.now() + 1000;
  while (!condition() && Date.now() < deadline) {
    Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 25);
  }
  return condition();
}

export function assertProcessStopped(pid) {
  const deadline = Date.now() + 1000;
  while (!isStopped(pid) && Date.now() < deadline) {
    Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 25);
  }
  assert.ok(isStopped(pid), `expected child process ${pid} to stop`);
}
