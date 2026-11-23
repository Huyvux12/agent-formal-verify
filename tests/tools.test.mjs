// Copyright (c) 2026 Michael Denyer
// SPDX-License-Identifier: GPL-3.0-only
import assert from "node:assert/strict";
import { spawn, spawnSync } from "node:child_process";
import { chmodSync, existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { afterEach, test } from "node:test";
import { assertProcessStopped, command, excludes, fakeTlc, fixture, includes, leanPin, removeFixtures, root, run, scripts, writeLeanProject } from "./helpers.mjs";

afterEach(removeFixtures);

test("missing runtimes are unavailable with their remedies", () => {
  const dir = fixture();
  const cases = [
    ["python-tools.sh", "require_python", {}, "install Python 3"],
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

test("the Lean checker and Lean setup report a missing elan as unavailable with its remedy", () => {
  const dir = fixture();
  writeFileSync(join(dir, "lean-toolchain"), leanPin + "\n");
  writeFileSync(join(dir, "lakefile.toml"), 'name = "model"\n');
  for (const args of [[join(scripts, "lean-check.sh"), dir], [join(scripts, "setup.sh"), "lean", dir]]) {
    const result = spawnSync("bash", args, { encoding: "utf8", env: { ...process.env, PATH: "/usr/bin:/bin" } });
    assert.equal(result.status, 3, result.stdout + result.stderr);
    assert.equal(result.stdout, "UNAVAILABLE elan is not on PATH; install elan from https://github.com/leanprover/elan\n");
  }
});

test("the Lean checker and Lean setup report a lean-toolchain pin they cannot read as a failure without a traceback", () => {
  const dir = fixture();
  writeLeanProject(dir);
  writeFileSync(join(dir, "lean-toolchain"), Buffer.from([0xff, 0xfe, 0x0a]));
  command(dir, "elan", "exit 0");
  for (const [script, args] of [["lean-check.sh", [dir]], ["setup.sh", ["lean", dir]]]) {
    const result = run(dir, script, args);
    assert.equal(result.status, 1, result.stdout + result.stderr);
    assert.ok(result.stdout.startsWith(`FAIL cannot read ${join(dir, "lean-toolchain")}: `), result.stdout);
    excludes(result.stderr, "Traceback");
  }
});

test("helpers report a python3 older than 3.9 as unavailable before running it", () => {
  const dir = fixture();
  writeFileSync(join(dir, "One.matrix"), "");
  command(dir, "python3", "echo 3.8.20\nexit 1");
  const java = command(dir, "java", "exit 0");
  const cases = [
    ["bash", [join(scripts, "tlc-matrix.sh"), join(dir, "One.matrix")]],
    ["bash", [join(scripts, "kani-check.sh"), dir]],
    ["bash", [join(scripts, "setup.sh"), "rust"]],
    ["bash", [join(scripts, "setup.sh"), "storage"]],
    ["bash", [join(scripts, "setup.sh"), "tla"]],
    ["bash", [join(scripts, "setup.sh"), "lean", dir]],
  ];
  for (const [shell, args] of cases) {
    const result = spawnSync(shell, args, { encoding: "utf8", env: { ...process.env, PATH: `${join(dir, "bin")}:${process.env.PATH}`, JAVA: java } });
    assert.equal(result.status, 3, args.join(" ") + ": " + result.stdout + result.stderr);
    assert.equal(result.stdout, "UNAVAILABLE python3 is Python 3.8.20; install Python 3.9 or later\n", args.join(" "));
  }
});

test("the mutation runner reports a Python older than 3.9 as unavailable when run directly", () => {
  const script = [
    "import runpy, sys",
    `sys.path.insert(0, ${JSON.stringify(scripts)})`,
    "sys.version_info = (3, 8, 20, 'final', 0)",
    `sys.argv = ['mutate.py', 'Name.mutations']`,
    `runpy.run_path(${JSON.stringify(join(scripts, "mutate.py"))}, run_name='__main__')`,
  ].join("\n");
  const result = spawnSync("python3", ["-B", "-c", script], { cwd: root, encoding: "utf8" });
  assert.equal(result.status, 3, result.stdout + result.stderr);
  assert.equal(result.stdout, "UNAVAILABLE python3 is Python 3.8.20; install Python 3.9 or later\n");
});

test("helper usage errors exit 2", () => {
  const dir = fixture();
  for (const [script, args] of [["lean-check.sh", []], ["tlc-matrix.sh", []], ["mutate.py", []], ["setup.sh", ["lean"]], ["processes.py", []], ["storage.py", []]]) {
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

test("storage.parse_df_mounts selects only writable larger local volume directories", () => {
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
    "import storage",
    "devs = {'/': 1, '/tmp': 2, '/System/Volumes/Data': 2, '/etc/hosts': 3, '/Volumes/BackupRO': 4, '/Volumes/RecoveryX': 5, '/runner': 6, '/Volumes/ExternalLarge': 7}",
    "frees = {'/': 20*storage.GIB, '/tmp': 20*storage.GIB, '/etc/hosts': 500*storage.GIB, '/Volumes/BackupRO': 500*storage.GIB, '/Volumes/RecoveryX': 100*storage.GIB, '/runner': 150*storage.GIB, '/Volumes/ExternalLarge': 300*storage.GIB}",
    "stat_fn = lambda p: types.SimpleNamespace(st_dev=devs[str(p)], st_mode=stat.S_IFREG if str(p) == '/etc/hosts' else stat.S_IFDIR)",
    "access_fn = lambda p, _m: str(p) != '/Volumes/BackupRO'",
    "usage_fn = lambda p: types.SimpleNamespace(free=frees[str(p)])",
    `out = storage.parse_df_mounts(${JSON.stringify(dfSample)}, '/tmp', '/', stat_fn=stat_fn, access_fn=access_fn, usage_fn=usage_fn)`,
    "report = storage.format_report(storage.StorageReport('/Volumes/ExternalLarge/.tmp', 300*storage.GIB, 20*storage.GIB, False, 64, (('/Volumes/Big Disk', 400*storage.GIB),)))",
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

test("an explicitly configured TMPDIR that cannot be created fails cleanly without falling back", () => {
  const dir = fixture();
  const blocker = join(dir, "not-a-dir");
  writeFileSync(blocker, "file");
  const badTmp = join(blocker, "nested");
  writeFileSync(join(dir, "One.tla"), "---- MODULE One ----\nStep == x + 1\n====\n");
  writeFileSync(join(dir, "One.matrix"), "spec One.tla\ncheck INVARIANTS Small\nrun n=1 | N=1\n");
  writeFileSync(join(dir, "One.mutations"), "mutation m\ndetects Small\n- x + 1\n+ x\n");
  writeFileSync(join(dir, "tools.jar"), "user supplied");
  for (const [script, args] of [
    ["setup.sh", ["storage"]],
    ["tlc-matrix.sh", [join(dir, "One.matrix")]],
    ["mutate.py", [join(dir, "One.mutations")]],
  ]) {
    const result = run(dir, script, args, {
      JAVA: fakeTlc(dir, 'echo "Model checking completed. No error has been found."'),
      TLC_JAR: join(dir, "tools.jar"),
      TMPDIR: badTmp,
    });
    assert.equal(result.status, 1, script + ": " + result.stdout + result.stderr);
    includes(result.stdout, "TMPDIR");
    excludes(result.stderr, "Traceback");
  }
});

test("tlc-matrix warns on stderr once per run when FORMAL_MIN_FREE_GIB exceeds available temp space", () => {
  const dir = fixture();
  writeFileSync(join(dir, "One.tla"), "---- MODULE One ----\nStep == x + 1\n====\n");
  writeFileSync(join(dir, "One.matrix"), "spec One.tla\ncheck INVARIANTS Small\nrun n=1 | N=1\n");
  writeFileSync(join(dir, "One.mutations"), "mutation m\ndetects Small\n- x + 1\n+ x \\* BUG\n");
  writeFileSync(join(dir, "tools.jar"), "user supplied");
  const java = fakeTlc(dir, [
    'for last; do :; done',
    'if grep -q BUG "$last"; then echo "Error: Invariant Small is violated."; exit 12; fi',
    'echo "Model checking completed. No error has been found."; echo "4 distinct states found"',
  ].join("\n"));
  const matrix = run(dir, "tlc-matrix.sh", [join(dir, "One.matrix")], {
    JAVA: java, TLC_JAR: join(dir, "tools.jar"), FORMAL_MIN_FREE_GIB: "999999",
  });
  assert.equal(matrix.status, 0, matrix.stdout + matrix.stderr);
  includes(matrix.stdout, "PASS One n=1 4 distinct states found");
  includes(matrix.stderr, "WARN low free space on temp dir");

  const mutated = run(dir, "mutate.py", [join(dir, "One.mutations")], {
    JAVA: java, TLC_JAR: join(dir, "tools.jar"), FORMAL_MIN_FREE_GIB: "999999",
  });
  assert.equal(mutated.status, 0, mutated.stdout + mutated.stderr);
  assert.equal(mutated.stderr.match(/WARN low free space on temp dir/g)?.length, 1, mutated.stderr);
});

// Each tool's readiness probe sleeps in a child that records the check's pid, the probe's and its own, then succeeds,
// so a check that a signal does not stop goes on to print READY. The child runs in the foreground, as a JVM does,
// so a Ctrl-C reaches it.
const probe = (pids, after = "") => `bash -c 'echo "$1 $2 $$" > "$3"; exec sleep 3' probe "$PPID" "$$" "${pids}"\n${after}`;
const readiness = {
  tla(dir, pids) {
    writeFileSync(join(dir, "tools.jar"), "user supplied");
    return { args: ["tla"], env: { JAVA: command(dir, "java", `[ "$1" = "-version" ] && exit 0\n${probe(pids)}`), TLC_JAR: join(dir, "tools.jar") } };
  },
  rust(dir, pids) {
    const bundle = join(dir, "kani/kani-0.68.0");
    for (const path of ["bin/kani-compiler", "bin/cbmc", "toolchain/bin/rustc", "toolchain/bin/cargo", "bin/kani-driver"]) {
      mkdirSync(join(bundle, path, ".."), { recursive: true });
      writeFileSync(join(bundle, path), "#!/bin/bash\n" + (path === "bin/kani-driver" ? probe(pids, 'echo "Kani Rust Verifier 0.68.0 (cargo plugin)"') : "exit 0") + "\n");
      chmodSync(join(bundle, path), 0o755);
    }
    return { args: ["rust"], env: { KANI_HOME: join(dir, "kani") } };
  },
  lean(dir, pids) {
    const project = join(dir, "lean");
    writeLeanProject(project);
    command(dir, "elan", probe(pids));
    return { args: ["lean", project], env: {} };
  },
};

// Signal setup.sh while its readiness probe runs: the setup.sh process alone, or its whole process group as Ctrl-C does.
function signalSetup(tool, signal, group) {
  const dir = fixture();
  const pids = join(dir, "probe.pids");
  const { args, env } = readiness[tool](dir, pids);
  return new Promise((resolve) => {
    const child = spawn("bash", [join(scripts, "setup.sh"), ...args], {
      detached: group,
      env: { ...process.env, PATH: `${join(dir, "bin")}:${process.env.PATH}`, FORMAL_MIN_FREE_GIB: "0", ...env },
    });
    let stdout = "", sent, ended;
    child.stdout.on("data", (data) => (stdout += data));
    const timer = setInterval(() => {
      if (existsSync(pids) && readFileSync(pids, "utf8").endsWith("\n")) {
        clearInterval(timer);
        sent = Date.now();
        process.kill(group ? -child.pid : child.pid, signal);
      }
    }, 20);
    child.on("exit", (exitCode, signalName) => {
      clearInterval(timer);
      ended = { exitCode, signalName, elapsed: Date.now() - sent };
    });
    // Read stdout until every process that holds it has closed it, so a check left running is heard from.
    child.on("close", () => resolve({ ...ended, stdout, pids: readFileSync(pids, "utf8").trim().split(" ").map(Number) }));
  });
}

for (const tool of Object.keys(readiness)) {
  for (const signal of ["SIGINT", "SIGTERM", "SIGHUP"]) {
    test(`${signal} sent to setup.sh ${tool} alone stops its readiness check, prints no READY and ends setup.sh by ${signal}`, async () => {
      const result = await signalSetup(tool, signal, false);
      for (const pid of result.pids) assertProcessStopped(pid);
      excludes(result.stdout, "READY");
      assert.equal(result.signalName, signal, JSON.stringify(result));
      assert.ok(result.elapsed < 2000, JSON.stringify(result));
    });
  }

  test(`Ctrl-C to setup.sh ${tool}'s process group stops its readiness check and ends setup.sh by SIGINT`, async () => {
    const result = await signalSetup(tool, "SIGINT", true);
    for (const pid of result.pids) assertProcessStopped(pid);
    excludes(result.stdout, "READY");
    assert.equal(result.signalName, "SIGINT", JSON.stringify(result));
  });
}
