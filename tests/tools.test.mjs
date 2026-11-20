// Copyright (c) 2026 Michael Denyer
// SPDX-License-Identifier: GPL-3.0-only
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { afterEach, test } from "node:test";
import { command, excludes, fixture, includes, leanPin, removeFixtures, root, run, scripts } from "./helpers.mjs";

afterEach(removeFixtures);

test("missing runtimes and hash tools are unavailable with their remedies", () => {
  const dir = fixture();
  const jar = join(dir, "tools.jar");
  writeFileSync(jar, "jar");
  writeFileSync(join(dir, "lean-toolchain"), leanPin + "\n");
  const java = command(dir, "java", "exit 0");
  const cases = [
    ["tlc-tools.sh", "require_tlc_runtime", { JAVA: "/absent/java" }, "install a JDK"],
    ["tlc-tools.sh", "require_tlc_runtime", { JAVA: java }, "install Python 3"],
    ["tlc-tools.sh", 'check_tlc_jar "$TASK_JAR"', { TASK_JAR: jar }, "install sha256sum or shasum"],
    ["lean-tools.sh", 'lean_pin "$TASK_PROJECT"', { TASK_PROJECT: dir }, "install elan"],
  ];
  for (const [script, call, extra, remedy] of cases) {
    const result = spawnSync("/bin/bash", ["-c", 'source "$1"; ' + call, "bash", join(scripts, script)], {
      encoding: "utf8", env: { ...process.env, PATH: join(dir, "bin"), ...extra },
    });
    assert.equal(result.status, 3, result.stdout + result.stderr);
    assert.ok(result.stdout.startsWith("UNAVAILABLE "), result.stdout);
    includes(result.stdout, remedy);
    excludes(result.stdout, "PASS");
    excludes(result.stdout, "SUMMARY");
  }
});

test("helper usage errors exit 2", () => {
  const dir = fixture();
  for (const [script, args] of [["lean-check.sh", []], ["tlc-matrix.sh", []], ["mutate.py", []], ["setup.sh", ["lean"]], ["workdir.py", []]]) {
    assert.equal(run(dir, script, args).status, 2, script);
  }
});

test("setup.sh storage warns when free space is below FORMAL_MIN_FREE_GIB", () => {
  const dir = fixture();
  const tmp = join(dir, "custom-tmp");
  const result = run(dir, "setup.sh", ["storage"], { TMPDIR: tmp, FORMAL_MIN_FREE_GIB: "999999" });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  includes(result.stdout, "TEMP_DIR ");
  includes(result.stdout, "WARN low free space (< 999999 GiB):");
});

test("workdir.parse_df_mounts selects only writable larger local volume directories", () => {
  const dir = fixture();
  mkdirSync(join(dir, "tmp"));
  const dfSample = [
    "Filesystem 1024-blocks Used Available Capacity Mounted on",
    "/dev/disk3s1s1 400000 300000 100000 75% /",
    "/dev/disk3s5 400000 300000 100000 75% /System/Volumes/Data",
    "/dev/disk4s1 900000 100000 800000 11% /etc/hosts",
    "/dev/disk5s1 900000 100000 800000 11% /Volumes/BackupRO",
    "/dev/disk6s1 600000 100000 500000 16% /Volumes/RecoveryX",
    "/dev/disk7s1 700000 100000 600000 14% /runner",
    "/dev/disk8s1 1200000 100000 1100000 8% /Volumes/ExternalLarge",
  ].join("\n");
  const script = [
    "import json, stat, sys, types",
    `sys.path.insert(0, ${JSON.stringify(scripts)})`,
    "import workdir",
    "devs = {'/': 1, '/tmp': 2, '/System/Volumes/Data': 2, '/etc/hosts': 3, '/Volumes/BackupRO': 4, '/Volumes/RecoveryX': 5, '/runner': 6, '/Volumes/ExternalLarge': 7}",
    "frees = {'/': 20*workdir.GIB, '/tmp': 20*workdir.GIB, '/etc/hosts': 500*workdir.GIB, '/Volumes/BackupRO': 500*workdir.GIB, '/Volumes/RecoveryX': 100*workdir.GIB, '/runner': 150*workdir.GIB, '/Volumes/ExternalLarge': 300*workdir.GIB}",
    "stat_fn = lambda p: types.SimpleNamespace(st_dev=devs[str(p)], st_mode=stat.S_IFREG if str(p) == '/etc/hosts' else stat.S_IFDIR)",
    "access_fn = lambda p, _m: str(p) != '/Volumes/BackupRO'",
    "usage_fn = lambda p: types.SimpleNamespace(free=frees[str(p)])",
    `out = workdir.parse_df_mounts(${JSON.stringify(dfSample)}, '/tmp', '/', stat_fn=stat_fn, access_fn=access_fn, usage_fn=usage_fn)`,
    "report = workdir.format_report(workdir.StorageReport('/Volumes/ExternalLarge/.tmp', 300*workdir.GIB, 20*workdir.GIB, False, 64, (('/Volumes/Big Disk', 400*workdir.GIB),)))",
    "print(json.dumps({'mounts': out, 'report': report}))",
  ].join("; ");
  const result = spawnSync("python3", ["-B", "-c", script], { cwd: root, encoding: "utf8" });
  assert.equal(result.status, 0, result.stderr);
  const parsed = JSON.parse(result.stdout);
  assert.deepEqual(parsed.mounts, [
    ["/Volumes/ExternalLarge", 300 * 1024 ** 3],
    ["/runner", 150 * 1024 ** 3],
    ["/Volumes/RecoveryX", 100 * 1024 ** 3],
  ]);
  assert.deepEqual(parsed.report, [
    `TEMP_DIR /Volumes/ExternalLarge/.tmp (300.0 GiB free)`,
    `SYSTEM_DISK / (20.0 GiB free)`,
    `EXTERNAL_VOLUME /Volumes/Big Disk (400.0 GiB free; suggested TMPDIR='/Volumes/Big Disk/.tmp/formal-verify')`,
  ]);
});
