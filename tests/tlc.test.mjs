// Copyright (c) 2026 Michael Denyer
// SPDX-License-Identifier: GPL-3.0-only
import assert from "node:assert/strict";
import { spawn, spawnSync } from "node:child_process";
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { afterEach, test } from "node:test";
import { command, excludes, fakeTlc, fixture, includes, leanPin, logs, removeFixtures, root, run, scripts, writeLeanProject } from "./helpers.mjs";

afterEach(removeFixtures);

test("TLC setup names the release to fetch when the pinned JAR is missing, without downloading it", () => {
  const dir = fixture();
  command(dir, "curl", 'echo download >> "$TASK_TRACE"; exit 99');
  const result = run(dir, "setup.sh", ["tla"], { TLC_CACHE: join(dir, "cache") });
  assert.equal(result.status, 3);
  includes(result.stdout, "UNAVAILABLE " + join(dir, "cache/tla2tools-v1.7.4.jar") + " is missing");
  includes(result.stdout, "https://github.com/tlaplus/tlaplus/releases/tag/v1.7.4");
  assert.equal(existsSync(join(dir, "calls")), false);
  assert.equal(existsSync(join(dir, "cache")), false);
});

test("TLC setup rejects a cached JAR that does not match the pin", () => {
  const dir = fixture();
  mkdirSync(join(dir, "cache"));
  writeFileSync(join(dir, "cache/tla2tools-v1.7.4.jar"), "truncated");
  const result = run(dir, "setup.sh", ["tla"], { TLC_CACHE: join(dir, "cache") });
  assert.equal(result.status, 3);
  includes(result.stdout, "UNAVAILABLE ");
  includes(result.stdout, "has sha256");
});

test("TLC verification reports a supplied JAR that does not exist", () => {
  const dir = fixture();
  const matrix = join(dir, "empty.matrix");
  writeFileSync(matrix, "");
  const result = run(dir, "tlc-matrix.sh", [matrix], { TLC_JAR: join(dir, "absent.jar") });
  assert.equal(result.status, 3);
  includes(result.stdout, "UNAVAILABLE ");
  includes(result.stdout, "does not exist");
});

test("TLC setup accepts an explicitly supplied local JAR", () => {
  const dir = fixture();
  const jar = join(dir, "local tools.jar");
  writeFileSync(jar, "user supplied");
  const result = run(dir, "setup.sh", ["tla"], { TLC_JAR: jar });
  assert.equal(result.status, 0);
  includes(result.stdout, "READY TLC " + jar);
});

function reduce(log) {
  return spawnSync("python3", [join(scripts, "tlc-trace.py"), join(logs, log)], { encoding: "utf8" });
}

test("the trace reducer shows only changed variables for an invariant violation", () => {
  const result = reduce("tlc-invariant.log");
  assert.equal(result.status, 0);
  assert.equal(result.stdout, [
    "--- state 1: Initial predicate",
    "    x = 0",
    "    y = 0",
    "--- state 2: Step",
    "    x = 1",
    "--- state 3: Step",
    "    x = 2",
    "    y = 1",
    "--- state 4: Step",
    "    x = 3",
    "",
  ].join("\n"));
});

test("the trace reducer keeps the lasso of a liveness counter-example", () => {
  const result = reduce("tlc-liveness.log");
  assert.equal(result.status, 0);
  includes(result.stdout, "--- state 3: Step\n    x = 2\n    y = 1\n--- Back to state 1");
});

test("the trace reducer reads a one-variable spec and its multi-line values", () => {
  const result = reduce("tlc-one-variable.log");
  assert.equal(result.status, 0);
  includes(result.stdout, "--- state 1: Initial predicate\n    x = <<>>\n--- state 2: Next\n    x = << [ id |-> 0,");
  includes(result.stdout, "   [ id |-> 1,");
});

test("the trace reducer fails on a log without an error trace", () => {
  const result = reduce("lake-sorry.log");
  assert.equal(result.status, 1);
  assert.equal(result.stdout, "");
});

function matrixFixture(lines, java, log = "tlc-invariant.log") {
  const dir = fixture();
  for (const sub of ["a", "b"]) mkdirSync(join(dir, sub));
  writeFileSync(join(dir, "a/One.tla"), "---- MODULE One ----\n====\n");
  writeFileSync(join(dir, "a/Helper.tla"), "---- MODULE Helper ----\n====\n");
  writeFileSync(join(dir, "b/Two.tla"), "---- MODULE Two ----\n====\n");
  writeFileSync(join(dir, "checks.matrix"), lines.join("\n") + "\n");
  writeFileSync(join(dir, "tools.jar"), "user supplied");
  const passing = 'echo "Model checking completed. No error has been found."; echo "4 distinct states found"';
  return {
    dir,
    matrix: (args = []) => run(dir, "tlc-matrix.sh", [join(dir, "checks.matrix"), ...args], {
      JAVA: fakeTlc(dir, java ?? passing),
      TLC_JAR: join(dir, "tools.jar"),
      TLC_LOG: join(logs, log),
    }),
  };
}

test("the matrix runner reduces the trace of an invariant violation", () => {
  const { matrix } = matrixFixture(["spec a/One.tla", "check INVARIANTS Small", "run n=4 | N=4"], 'cat "$TLC_LOG"; exit 12');
  const result = matrix();
  assert.equal(result.status, 1);
  includes(result.stdout, "FAIL One n=4: Error: Invariant Small is violated.");
  includes(result.stdout, "--- state 4: Step\n    x = 3\n");
  excludes(result.stdout, "/\\ y = 1");
});

test("the matrix runner reports the final state count, not a progress line's", () => {
  const { matrix } = matrixFixture(["spec a/One.tla", "run n=450 | N=450"], [
    'echo "Progress(294) at 2026-10-01 17:24:40: 12,610,693 states generated (12,610,693 s/min), 4,246,783 distinct states found (4,246,783 ds/min), 43,235 states left on queue."',
    'echo "Model checking completed. No error has been found."',
    'echo "274591352 states generated, 91733851 distinct states found, 0 states left on queue."',
  ].join("\n"));
  assert.equal(matrix().stdout, "PASS One n=450 91733851 distinct states found\nSUMMARY 1 of 1 runs passed, 91733851 distinct states in total\n");
});

test("the matrix runner totals the passing runs and their state counts", () => {
  const { matrix } = matrixFixture(
    ["spec a/One.tla", "run small | N=1", "run large | N=2", "spec a/Gone.tla", "run lost | N=1"],
    'echo "Model checking completed. No error has been found."; echo "9,000 states generated, 1,204 distinct states found, 0 states left on queue."',
  );
  const result = matrix();
  assert.equal(result.status, 1);
  includes(result.stdout, "SUMMARY 2 of 3 runs passed, 2408 distinct states in total\n");
});

test("the matrix runner gives each run only its own spec directory's modules", () => {
  const { dir, matrix } = matrixFixture(
    ["spec a/One.tla", "run first | N=1", "\t", "spec b/Two.tla", "run second |"],
    'for last; do :; done; ls "$(dirname "$last")" | grep tla$ | tr "\\n" " " >> "$TASK_TRACE"; echo >> "$TASK_TRACE"\n' +
      'echo "Model checking completed. No error has been found."',
  );
  const result = matrix();
  excludes(result.stdout, "unknown directive");
  assert.equal(result.status, 0);
  assert.equal(readFileSync(join(dir, "calls"), "utf8"), "Helper.tla One.tla \nTwo.tla \n");
});

test("matrix checks affect only subsequent runs and reset at the next spec", () => {
  const { dir, matrix } = matrixFixture([
    "spec a/One.tla", "check INVARIANTS Early", "run first | N=1",
    "check PROPERTIES Later", "run second | N=2", "spec a/One.tla", "run third | N=3",
  ], [
    "for last; do :; done",
    'grep -E "^(INVARIANTS|PROPERTIES)" "$(dirname "$last")/MC.cfg" >> "$TASK_TRACE"',
    'echo END >> "$TASK_TRACE"',
    'echo "Model checking completed. No error has been found."',
  ].join("\n"));
  assert.equal(matrix().status, 0);
  assert.equal(readFileSync(join(dir, "calls"), "utf8"), "INVARIANTS Early\nEND\nINVARIANTS Early\nPROPERTIES Later\nEND\nEND\n");
});

test("the matrix runner reports a missing spec in one line without starting TLC", () => {
  const { dir, matrix } = matrixFixture(["spec a/Gone.tla", "run only | N=1"], 'echo started >> "$TASK_TRACE"');
  const result = matrix();
  assert.equal(result.status, 1);
  assert.equal(result.stdout, "FAIL Gone only: spec a/Gone.tla not found\nSUMMARY 0 of 1 runs passed, 0 distinct states in total\n");
  assert.equal(result.stderr, "");
  assert.equal(existsSync(join(dir, "calls")), false);
});

test("the matrix runner names the matrix when it has no runs and the filter when none match", () => {
  const { dir, matrix } = matrixFixture(["spec a/One.tla"]);
  assert.equal(matrix().stdout, `FAIL no run in ${join(dir, "checks.matrix")}\n`);
  assert.equal(matrix(["absent"]).stdout, `FAIL no run matching 'absent' in ${join(dir, "checks.matrix")}\n`);
});

test("the matrix runner fails a check line that no spec would keep", () => {
  const { matrix } = matrixFixture(["check INVARIANTS Small", "spec a/One.tla", "run n=4 | N=4"]);
  const result = matrix();
  assert.equal(result.status, 1);
  includes(result.stdout, "FAIL check 'INVARIANTS Small' before any spec line");
});

test("the matrix runner reads a matrix that holds bytes that are not UTF-8", () => {
  const { dir, matrix } = matrixFixture([]);
  writeFileSync(join(dir, "checks.matrix"), Buffer.concat([Buffer.from("# caf"), Buffer.from([0xe9]), Buffer.from("\nspec a/One.tla\nrun n=1 | N=1\n")]));
  const result = matrix();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  includes(result.stdout, "PASS One n=1 4 distinct states found\n");
});

test("the matrix runner fails a run line without a bar instead of inventing a constant", () => {
  const { dir, matrix } = matrixFixture(["spec a/One.tla", "run n=4"], 'echo started >> "$TASK_TRACE"');
  const result = matrix();
  assert.equal(result.status, 1);
  includes(result.stdout, "FAIL run 'n=4' has no | before its constants");
  assert.equal(existsSync(join(dir, "calls")), false);
});

test("an existing JAR whose TLC entry point cannot run is unavailable", () => {
  const dir = fixture();
  const jar = join(dir, "bad.jar");
  writeFileSync(jar, "not a jar");
  const matrix = join(dir, "One.matrix");
  writeFileSync(matrix, "spec One.tla\nrun n=1 | N=1\n");
  const java = command(dir, "bad-java", '[ "$1" = "-version" ] && exit 0\necho "Could not find or load main class tlc2.TLC" >&2; exit 1');
  for (const [script, args] of [["setup.sh", ["tla"]], ["tlc-matrix.sh", [matrix]]]) {
    const result = run(dir, script, args, { JAVA: java, TLC_JAR: jar });
    assert.equal(result.status, 3, result.stdout);
    assert.ok(result.stdout.startsWith("UNAVAILABLE "), result.stdout);
    includes(result.stdout, "tlc2.TLC");
    excludes(result.stdout, "READY");
    excludes(result.stdout, "SUMMARY");
  }
});

test("the pinned TLC help command may return 1 after printing its help", () => {
  const dir = fixture();
  const jar = join(dir, "tools.jar");
  writeFileSync(jar, "supplied");
  const java = command(dir, "help-java", '[ "$1" = "-version" ] && exit 0\necho "TLC - provides model checking and simulation of TLA+ specifications - Version 2.19"; exit 1');
  const result = run(dir, "setup.sh", ["tla"], { JAVA: java, TLC_JAR: jar });
  assert.equal(result.status, 0, result.stdout);
  includes(result.stdout, "READY TLC");
});

const reachJava = [
  'for last; do :; done',
  'dir=$(dirname "$last")',
  'if grep -q "^INVARIANT Reach" "$dir/MC.cfg"; then',
  '  name=$(sed -n "s/^INVARIANT //p" "$dir/MC.cfg")',
  '  sed "s/ReachNegated/$name/g" "$TLC_LOG"',
  '  exit 12',
  'fi',
  'echo "Model checking completed. No error has been found."',
  'echo "4 distinct states found"',
].join("\n");

const reachFixture = (lines, java = reachJava, log = "tlc-reach.log") => matrixFixture(lines, java, log);

test("reach checks report the shortest witness and count separately", () => {
  const { matrix } = reachFixture(["spec a/One.tla", "reach Full | n=1", "run n=1 | N=1"]);
  const result = matrix();
  assert.equal(result.status, 0);
  includes(result.stdout, "PASS One reach Full n=1: shortest trace 2 states (1 transitions)");
  includes(result.stdout, "SUMMARY 1 of 1 runs passed, 1 of 1 reach checks passed, 4 distinct states in total");
});

test("reach checks recognize an initial-state witness", () => {
  const { matrix } = reachFixture(["spec a/One.tla", "reach Full | n=1", "run n=1 | N=1"], reachJava, "tlc-reach-initial.log");
  const result = matrix();
  assert.equal(result.status, 0);
  includes(result.stdout, "shortest trace 1 states (0 transitions)");
});

test("an exhaustive reach search without a witness fails", () => {
  const { matrix } = reachFixture(["spec a/One.tla", "reach Full | n=1", "run n=1 | N=1"], 'echo "Model checking completed. No error has been found."');
  const result = matrix();
  assert.equal(result.status, 1);
  includes(result.stdout, "FAIL One reach Full n=1: the model never reaches this state");
  includes(result.stdout, "0 of 1 reach checks passed");
});

test("reach parsing rejects missing spec, operator, separator, or label", () => {
  for (const directive of ["reach Full | n=1", "spec a/One.tla\nreach Full", "spec a/One.tla\nreach Full |", "spec a/One.tla\nreach | n=1", "spec a/One.tla\nreach Full() | n=1"]) {
    const { matrix } = reachFixture([directive, "spec a/One.tla", "run n=1 | N=1"]);
    assert.equal(matrix().status, 1, directive);
  }
});

test("reach reports unmatched labels and resets at the next spec", () => {
  const { matrix } = reachFixture(["spec a/One.tla", "reach Full | absent", "run n=1 | N=1", "spec b/Two.tla", "run absent | N=1"]);
  const result = matrix();
  assert.equal(result.status, 1);
  includes(result.stdout, "reach Full: no run matching 'absent'");
  excludes(result.stdout, "PASS Two reach");
});

test("reach chooses the first matching run even when declared after it", () => {
  const { dir, matrix } = reachFixture(["spec a/One.tla", "run n=1 first | N=1", "run n=1 second | N=2", "reach Full | n=1"],
    'for last; do :; done\ngrep "N =" "$(dirname "$last")/MC.cfg" >> "$TASK_TRACE"\n' + reachJava);
  assert.equal(matrix().status, 0);
  assert.equal(readFileSync(join(dir, "calls"), "utf8"), "  N = 1\n  N = 2\n  N = 1\n");
  const filtered = matrix(["second"]);
  assert.equal(filtered.status, 0);
  excludes(filtered.stdout, "PASS One reach");
});

test("reach uses one worker and disables deadlock only for witness searches", () => {
  const { dir, matrix } = reachFixture(["spec a/One.tla", "reach Full | n=1", "run n=1 | N=1"],
    'printf "%s\\n" "$*" >> "$TASK_TRACE"\n' + reachJava);
  assert.equal(matrix().status, 0);
  const calls = readFileSync(join(dir, "calls"), "utf8").trim().split("\n");
  excludes(calls[0], "-deadlock");
  includes(calls[1], "-workers 1");
  includes(calls[1], "-deadlock");
});

test("each TLC run gets its own existing java.io.tmpdir", () => {
  const { dir, matrix } = matrixFixture(["spec a/One.tla", "run first | N=1", "run second | N=2"], [
    'for arg; do case "$arg" in -Djava.io.tmpdir=*) tmp=${arg#-Djava.io.tmpdir=}; [ -d "$tmp" ] && echo "$tmp" >> "$TASK_TRACE";; esac; done',
    'echo "Model checking completed. No error has been found."',
    'echo "4 distinct states found"',
  ].join("\n"));
  assert.equal(matrix().status, 0);
  const tmpdirs = existsSync(join(dir, "calls")) ? readFileSync(join(dir, "calls"), "utf8").trim().split("\n") : [];
  assert.equal(tmpdirs.length, 2, `java.io.tmpdir per launch: ${JSON.stringify(tmpdirs)}`);
  assert.notEqual(tmpdirs[0], tmpdirs[1]);
});

test("reach does not confuse a runtime error with an unreachable state", () => {
  const { matrix } = reachFixture(["spec a/One.tla", "reach Full | n=1", "run n=1 | N=1"], 'echo "Error: undefined operator Full"; exit 1');
  const result = matrix();
  assert.equal(result.status, 1);
  excludes(result.stdout, "the model never reaches this state");
  includes(result.stdout, "undefined operator Full");
});

test("reach searches do not inherit ordinary checks", () => {
  const { dir, matrix } = reachFixture(["spec a/One.tla", "check INVARIANTS Small", "check PROPERTIES Ends", "reach Full | n=1", "run n=1 | N=1"],
    'for last; do :; done\ngrep -E "^(INVARIANT|PROPERT)" "$(dirname "$last")/MC.cfg" >> "$TASK_TRACE"\n' + reachJava);
  assert.equal(matrix().status, 0);
  const checks = readFileSync(join(dir, "calls"), "utf8").trim().split("\n");
  assert.equal(checks.length, 3);
  assert.equal(checks[0], "INVARIANTS Small");
  assert.equal(checks[1], "PROPERTIES Ends");
  assert.match(checks[2], /^INVARIANT Reach[a-f0-9]+Negated$/);
});

test("a different invariant violation cannot pass a reach check", () => {
  const { matrix } = reachFixture(["spec a/One.tla", "reach Full | n=1", "run n=1 | N=1"], 'echo "Error: Invariant Other is violated."; echo "State 1: <Init>"; exit 12');
  const result = matrix();
  assert.equal(result.status, 1);
  excludes(result.stdout, "PASS One reach");
  excludes(result.stdout, "the model never reaches this state");
});

test("the matrix runner rejects empty or unsupported checks", () => {
  for (const check of ["check", "check INVARIANTS", "check UNKNOWN Small"]) {
    const { matrix } = matrixFixture(["spec a/One.tla", check, "run n=1 | N=1"]);
    const result = matrix();
    assert.equal(result.status, 1);
    includes(result.stdout, "malformed check");
  }
});

test("the matrix runner strips trailing spaces and tabs before | in run labels", () => {
  const { matrix } = matrixFixture([
    "run before-spec   \t | N=1",
    "spec a/One.tla",
    "run small-case     | N=1",
    "run multi  word\t  | N=2",
  ]);
  const result = matrix();
  assert.equal(result.status, 1);
  includes(result.stdout, "FAIL run 'before-spec' before any spec line\n");
  includes(result.stdout, "PASS One small-case 4 distinct states found\n");
  includes(result.stdout, "PASS One multi  word 4 distinct states found\n");
  const filtered = matrix(["small-case"]);
  assert.equal(filtered.stdout, "FAIL run 'before-spec' before any spec line\nPASS One small-case 4 distinct states found\nSUMMARY 1 of 1 runs passed, 4 distinct states in total\n");
});

test("invalid TLC_TIMEOUT settings are reported as unavailable without starting TLC", () => {
  const dir = fixture();
  writeFileSync(join(dir, "One.tla"), "---- MODULE One ----\n====\n");
  writeFileSync(join(dir, "One.matrix"), "spec One.tla\nrun n=1 | N=1\n");
  writeFileSync(join(dir, "tools.jar"), "user supplied");
  for (const value of ["0", "-5", "abc", "4294967296"]) {
    const result = run(dir, "tlc-matrix.sh", [join(dir, "One.matrix")], {
      JAVA: fakeTlc(dir, 'echo started >> "$TASK_TRACE"'),
      TLC_JAR: join(dir, "tools.jar"),
      TLC_TIMEOUT: value,
    });
    assert.equal(result.status, 3, value);
    assert.ok(result.stdout.startsWith("UNAVAILABLE "), result.stdout);
    includes(result.stdout, "TLC_TIMEOUT");
  }
  assert.equal(existsSync(join(dir, "calls")), false);
});

test("the matrix runner deletes each run directory as soon as the run finishes", () => {
  const dir = fixture();
  const customTmp = join(dir, "work-tmp");
  writeFileSync(join(dir, "One.tla"), "---- MODULE One ----\n====\n");
  writeFileSync(join(dir, "One.matrix"), "spec One.tla\nrun first | N=1\nrun second | N=2\n");
  writeFileSync(join(dir, "tools.jar"), "user supplied");
  const java = fakeTlc(dir, [
    'for last; do :; done',
    'run_dir=$(dirname "$last")',
    'work_dir=$(dirname "$run_dir")',
    'mkdir -p "$run_dir/states"',
    'echo state-data > "$run_dir/states/mock.fp"',
    'ls -1 "$work_dir" | wc -l | tr -d " " >> "$TASK_TRACE"',
    'echo "Model checking completed. No error has been found."',
    'echo "4 distinct states found"',
  ].join("\n"));
  const result = run(dir, "tlc-matrix.sh", [join(dir, "One.matrix")], {
    JAVA: java,
    TLC_JAR: join(dir, "tools.jar"),
    TMPDIR: customTmp,
    FORMAL_MIN_FREE_GIB: "0",
  });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  // Each run sees only its own single run.* dir because the prior run.* was deleted.
  assert.equal(readFileSync(join(dir, "calls"), "utf8"), "1\n1\n");
  assert.deepEqual(readdirSync(customTmp), []);
});

function isStopped(pid) {
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

function processesWhere(match) {
  const listing = spawnSync("ps", ["-A", "-ww", "-o", "pid=,command="], { encoding: "utf8" }).stdout;
  return listing.split("\n").map((line) => line.trim().split(/\s+/)).filter(([pid, ...command]) => pid && match(command.join(" "))).map(([pid]) => Number(pid));
}

function waitFor(condition) {
  const deadline = Date.now() + 1000;
  while (!condition() && Date.now() < deadline) {
    Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 25);
  }
  return condition();
}

function assertProcessStopped(pid) {
  const deadline = Date.now() + 1000;
  while (!isStopped(pid) && Date.now() < deadline) {
    Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 25);
  }
  assert.ok(isStopped(pid), `expected child process ${pid} to stop`);
}

test("timed-out TLC runs terminate their child process and report ordinary failure or incomplete reach", () => {
  const dir = fixture();
  writeFileSync(join(dir, "One.tla"), "---- MODULE One ----\n====\n");
  writeFileSync(join(dir, "One.matrix"), "spec One.tla\nreach Full | n=1\nrun n=1 | N=1\n");
  writeFileSync(join(dir, "tools.jar"), "user supplied");
  const pidFile = join(dir, "child.pid");
  const java = fakeTlc(dir, [
    'echo "Progress(1) at 2026-11-18 00:00:01: 100 states generated"',
    'echo "$$" > "$TASK_PID_FILE"',
    'exec sleep 30',
  ].join("\n"));
  const result = run(dir, "tlc-matrix.sh", [join(dir, "One.matrix")], {
    JAVA: java,
    TLC_JAR: join(dir, "tools.jar"),
    TLC_TIMEOUT: "1s",
    TASK_PID_FILE: pidFile,
  });
  assert.equal(result.status, 1);
  includes(result.stdout, "FAIL One n=1: TLC timed out after 1s; set TLC_TIMEOUT to change the limit");
  includes(result.stdout, "Progress(1)");
  includes(result.stdout, "FAIL One reach Full n=1: TLC did not complete the reach check");
  excludes(result.stdout, "the model never reaches this state");
  const pid = Number(readFileSync(pidFile, "utf8").trim());
  assertProcessStopped(pid);
});

test("long TLC runs forward elapsed time and Progress updates to stderr without changing stdout parsing", () => {
  const dir = fixture();
  writeFileSync(join(dir, "One.tla"), "---- MODULE One ----\n====\n");
  writeFileSync(join(dir, "One.matrix"), "spec One.tla\nrun n=1 | N=1\n");
  writeFileSync(join(dir, "tools.jar"), "user supplied");
  const java = fakeTlc(dir, [
    'echo "Progress(42) at 2026-11-18 00:00:01: 1,000 states generated, 500 distinct states found, 100 states left on queue."',
    'sleep 0.25',
    'echo "Model checking completed. No error has been found."',
    'echo "500 distinct states found"',
  ].join("\n"));
  const script = [
    "import sys",
    `sys.path.insert(0, ${JSON.stringify(scripts)})`,
    "import tlc",
    "tlc.PROGRESS_DELAY = 0.05",
    "tlc.PROGRESS_INTERVAL = 0.05",
    `sys.argv = ['tlc.py', ${JSON.stringify(join(dir, "One.matrix"))}]`,
    "sys.exit(tlc.main())",
  ].join("; ");
  const result = spawnSync("python3", ["-B", "-c", script], {
    cwd: root,
    encoding: "utf8",
    env: { ...process.env, JAVA: java, TLC_JAR: join(dir, "tools.jar") },
  });
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout, "PASS One n=1 500 distinct states found\nSUMMARY 1 of 1 runs passed, 500 distinct states in total\n");
  assert.match(result.stderr, /\[tlc\] One n=1: \d+s elapsed: Progress\(42\)/);
});
test("SIGTERM stops TLC and the processes it started, cleans temporary directories and ends the runner by SIGTERM", async () => {
  const dir = fixture();
  const customTmp = join(dir, "nested", "signal-tmp");
  writeFileSync(join(dir, "One.tla"), "---- MODULE One ----\n====\n");
  writeFileSync(join(dir, "One.matrix"), "spec One.tla\nrun hang | N=1\n");
  writeFileSync(join(dir, "tools.jar"), "user supplied");
  const pidFile = join(dir, "child.pid");
  const grandchildPidFile = join(dir, "grandchild.pid");
  const readyFile = join(dir, "ready");
  const java = fakeTlc(dir, [
    'for last; do :; done',
    'mkdir -p "$(dirname "$last")/states"',
    'echo data > "$(dirname "$last")/states/mock.fp"',
    'sleep 30 &',
    'echo "$!" > "$TASK_GRANDCHILD_PID_FILE"',
    'echo "$$" > "$TASK_PID_FILE"',
    'echo ready > "$TASK_READY_FILE"',
    'wait',
  ].join("\n"));
  let signalled;
  const code = await new Promise((resolve) => {
    const child = spawn("python3", [join(scripts, "tlc.py"), join(dir, "One.matrix")], {
      env: {
        ...process.env,
        JAVA: java,
        TLC_JAR: join(dir, "tools.jar"),
        TMPDIR: customTmp,
        TASK_PID_FILE: pidFile,
        TASK_GRANDCHILD_PID_FILE: grandchildPidFile,
        TASK_READY_FILE: readyFile,
        FORMAL_MIN_FREE_GIB: "0",
      },
    });
    const timer = setInterval(() => {
      if (existsSync(readyFile)) {
        clearInterval(timer);
        signalled = Date.now();
        child.kill("SIGTERM");
      }
    }, 20);
    child.on("close", (exitCode, signalName) => {
      clearInterval(timer);
      resolve({ exitCode, signalName, stopped: Date.now() - signalled });
    });
  });
  assertProcessStopped(Number(readFileSync(pidFile, "utf8").trim()));
  assertProcessStopped(Number(readFileSync(grandchildPidFile, "utf8").trim()));
  assert.deepEqual(readdirSync(customTmp), []);
  assert.equal(code.signalName, "SIGTERM", JSON.stringify(code));
  // TLC and its sleep die on SIGTERM, so the runner must not wait out the two seconds it allows,
  // even where nothing reaps the dead processes, as in a container whose first process never does.
  assert.ok(code.stopped < 1500, JSON.stringify(code));
});

test("SIGTERM also stops processes started while the runner is stopping TLC", async () => {
  const dir = fixture();
  writeFileSync(join(dir, "One.tla"), "---- MODULE One ----\n====\n");
  writeFileSync(join(dir, "One.matrix"), "spec One.tla\nrun hang | N=1\n");
  writeFileSync(join(dir, "tools.jar"), "user supplied");
  const realPs = spawnSync("sh", ["-c", "command -v ps"], { encoding: "utf8" }).stdout.trim();
  assert.ok(realPs, "ps must be on PATH");
  const psCalls = join(dir, "ps.calls");
  // Hold each listing back after ps takes it, so processes started meanwhile are missing from it.
  command(dir, "ps", `listing=$("${realPs}" "$@")\nsleep 0.2\necho call >> "${psCalls}"\nprintf '%s\\n' "$listing"`);
  const nap = `30.${process.pid}${Date.now() % 100000}`;
  const marker = `sleep ${nap}`;
  const readyFile = join(dir, "ready");
  const doneFile = join(dir, "done");
  const java = fakeTlc(dir, [
    "spawn() {",
    "  i=0",
    '  while [ "$i" -lt 200 ]; do',
    '    sleep "$TASK_NAP" &',
    "    i=$((i + 1))",
    '    if [ "$i" = 5 ]; then echo ready > "$TASK_READY_FILE"; fi',
    "    sleep 0.02",
    "  done",
    '  echo done > "$TASK_DONE_FILE"',
    "  wait",
    "}",
    "spawn &",
    "wait",
  ].join("\n"));
  const marked = () => processesWhere((command) => command === marker);
  const probe = spawn("sleep", [nap]);
  try {
    assert.ok(waitFor(() => marked().includes(probe.pid)), "the process search must find a marked sleep");
  } finally {
    probe.kill("SIGKILL");
  }
  const code = await new Promise((resolve) => {
    const child = spawn("python3", [join(scripts, "tlc.py"), join(dir, "One.matrix")], {
      env: {
        ...process.env,
        PATH: `${join(dir, "bin")}:${process.env.PATH}`,
        JAVA: java,
        TLC_JAR: join(dir, "tools.jar"),
        TASK_NAP: nap,
        TASK_READY_FILE: readyFile,
        TASK_DONE_FILE: doneFile,
        FORMAL_MIN_FREE_GIB: "0",
      },
    });
    const timer = setInterval(() => {
      if (existsSync(readyFile)) {
        clearInterval(timer);
        child.kill("SIGTERM");
      }
    }, 20);
    child.on("close", (exitCode, signalName) => {
      clearInterval(timer);
      resolve({ exitCode, signalName });
    });
  });
  try {
    assert.equal(code.signalName, "SIGTERM", JSON.stringify(code));
    assert.ok(existsSync(psCalls), "the runner must list processes with ps");
    assert.ok(!existsSync(doneFile), "TLC's processes started all their sleeps before the runner stopped them, so nothing was checked");
    assert.ok(waitFor(() => marked().length === 0), `still running: ${marked()}`);
  } finally {
    for (const find of [() => processesWhere((command) => command.includes(dir)), marked]) {
      for (const pid of find()) {
        try {
          process.kill(pid, "SIGKILL");
        } catch {
          // Already gone.
        }
      }
    }
  }
});

test("a second interrupt while the runner stops TLC does not leave TLC suspended", () => {
  const dir = fixture();
  const ps = spawnSync("sh", ["-c", "command -v ps"], { encoding: "utf8" }).stdout.trim();
  assert.ok(ps, "ps must be on PATH");
  writeFileSync(join(dir, "ps"), `#!/bin/sh\nkill -INT "$PPID"\nexec "${ps}" "$@"\n`, { mode: 0o755 });
  const script = [
    "import os, signal, subprocess, sys",
    `sys.path.insert(0, ${JSON.stringify(scripts)})`,
    "import workdir",
    "signal.signal(signal.SIGINT, signal.default_int_handler)",
    "checker = subprocess.Popen(['sleep', '30'])",
    "try:",
    "    try:",
    "        workdir.stop_process(checker)",
    "        print('not interrupted')",
    "    except KeyboardInterrupt:",
    "        print('interrupted')",
    "    try:",
    "        print('exited', checker.wait(timeout=5))",
    "    except subprocess.TimeoutExpired:",
    "        print('still suspended')",
    "finally:",
    "    checker.kill()",
    "    checker.wait()",
  ].join("\n");
  const result = spawnSync("python3", ["-B", "-c", script], {
    cwd: root,
    encoding: "utf8",
    env: { ...process.env, PATH: `${dir}:${process.env.PATH}` },
  });
  assert.equal(result.status, 0, result.stderr);
  assert.deepEqual(result.stdout.trim().split("\n"), ["interrupted", "exited -15"]);
});

test("stopping a checker that exits just after the runner checks it sends no signal to its freed pid", () => {
  const script = [
    "import os, signal, subprocess, sys, time",
    `sys.path.insert(0, ${JSON.stringify(scripts)})`,
    "import workdir",
    "checker = subprocess.Popen(['true'])",
    "# Wait for the exit without reaping the checker; macOS Python has no os.waitid.",
    "while not subprocess.run(['ps', '-o', 'stat=', '-p', str(checker.pid)], capture_output=True, text=True).stdout.strip().startswith('Z'):",
    "    time.sleep(0.01)",
    "# The first poll misses the exit, as it does when the checker exits right after it.",
    "polls = []",
    "real_poll = checker.poll",
    "def poll():",
    "    polls.append(1)",
    "    return None if len(polls) == 1 else real_poll()",
    "checker.poll = poll",
    "sent = []",
    "real_kill = os.kill",
    "def kill(pid, signum):",
    "    if pid != checker.pid:",
    "        return real_kill(pid, signum)",
    "    sent.append(signal.Signals(signum).name)",
    "os.kill = kill",
    "workdir.stop_process(checker)",
    "print(checker.returncode, sent)",
  ].join("\n");
  const result = spawnSync("python3", ["-B", "-c", script], { cwd: root, encoding: "utf8" });
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout.trim(), "0 []");
});

function stopChecker(dir, checker, settings = []) {
  const script = [
    "import os, subprocess, sys, time",
    `sys.path.insert(0, ${JSON.stringify(scripts)})`,
    "import workdir",
    ...settings,
    // A process the checker started keeps any pipe it inherits open, and spawnSync waits for the pipes to close.
    `checker = subprocess.Popen(['bash', '-c', ${JSON.stringify(checker)}, 'checker', sys.argv[1]], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)`,
    "open(sys.argv[1] + '.checker', 'w').write(str(checker.pid))",
    "while not (os.path.exists(sys.argv[1]) and open(sys.argv[1]).read().endswith('\\n')):",
    "    time.sleep(0.02)",
    "workdir.stop_process(checker)",
    "print(checker.returncode)",
  ].join("\n");
  const pidFile = join(dir, "sleep.pid");
  const result = spawnSync("python3", ["-B", "-c", script, pidFile], {
    cwd: root,
    encoding: "utf8",
    timeout: 10000,
    env: { ...process.env, PATH: `${join(dir, "bin")}:${process.env.PATH}` },
  });
  return { result, pid: Number(readFileSync(pidFile, "utf8")), checker: Number(readFileSync(`${pidFile}.checker`, "utf8")) };
}

function killAll(...pids) {
  for (const pid of pids) {
    try {
      process.kill(pid, "SIGKILL");
    } catch {
      // Already gone.
    }
  }
}

test("stopping a checker also kills a process it started that ignores SIGTERM", () => {
  const dir = fixture();
  const { result, pid } = stopChecker(dir, 'trap "" TERM; sleep 30 & echo "$!" > "$1"; wait');
  try {
    assert.equal(result.status, 0, result.stderr);
    assert.equal(result.stdout.trim(), "-9");
    assertProcessStopped(pid);
  } finally {
    try {
      process.kill(pid, "SIGKILL");
    } catch {
      // Already gone.
    }
  }
});

test("stopping a checker warns when ps cannot list the processes it started", () => {
  const dir = fixture();
  command(dir, "ps", "exit 1");
  const { result, pid } = stopChecker(dir, 'sleep 30 & echo "$!" > "$1"; wait');
  try {
    assert.equal(result.status, 0, result.stderr);
    assert.equal(result.stdout.trim(), "-15");
    includes(result.stderr, "WARN ps cannot list the processes that the checker started; they may still be running");
  } finally {
    try {
      process.kill(pid, "SIGKILL");
    } catch {
      // Already gone.
    }
  }
});

test("stopping a checker gives up on a ps that does not answer, signals the checker and warns", () => {
  const dir = fixture();
  command(dir, "ps", "exec sleep 30");
  const start = Date.now();
  const { result, pid, checker } = stopChecker(dir, 'sleep 30 & echo "$!" > "$1"; wait', ["workdir.PS_TIMEOUT = 0.5"]);
  try {
    assert.equal(result.status, 0, result.stderr);
    assert.equal(result.stdout.trim(), "-15");
    includes(result.stderr, "WARN ps cannot list the processes that the checker started; they may still be running");
    assert.ok(Date.now() - start < 5000, `the stop took ${Date.now() - start} ms`);
  } finally {
    killAll(pid, checker);
  }
});

test("stopping a checker stops listing after a bounded number of ps calls and warns", () => {
  const dir = fixture();
  const realPs = spawnSync("sh", ["-c", "command -v ps"], { encoding: "utf8" }).stdout.trim();
  const listings = join(dir, "listings");
  // Each listing names one more child of the checker, as a process that keeps starting others would.
  // The pids are above every system's pid limit, so their signals reach no process.
  command(dir, "ps", [
    `"${realPs}" "$@"`,
    'case "$*" in *ppid*) echo x >> "' + listings + '"; echo "$((5000000 + $(wc -l < "' + listings + '"))) $(cat "' + join(dir, "sleep.pid.checker") + '")" ;; esac',
  ].join("\n"));
  const { result, pid, checker } = stopChecker(dir, 'sleep 30 & echo "$!" > "$1"; wait', ["workdir.MAX_LISTINGS = 5"]);
  try {
    assert.equal(result.status, 0, result.stderr);
    assert.equal(result.stdout.trim(), "-15");
    includes(result.stderr, "WARN the checker kept starting processes through 5 ps listings; processes it started later may still be running");
    assert.equal(readFileSync(listings, "utf8").split("\n").filter(Boolean).length, 5);
  } finally {
    killAll(pid, checker);
  }
});

test("Ctrl-C stops a shell loop that runs the matrix runner", async () => {
  const dir = fixture();
  writeFileSync(join(dir, "One.tla"), "---- MODULE One ----\n====\n");
  writeFileSync(join(dir, "One.matrix"), "spec One.tla\nrun hang | N=1\n");
  writeFileSync(join(dir, "tools.jar"), "user supplied");
  const starts = join(dir, "starts");
  const java = fakeTlc(dir, 'echo start >> "$TASK_STARTS"\nexec sleep 30');
  const result = await new Promise((resolve) => {
    const child = spawn("bash", ["-c", 'for i in 1 2; do bash "$1" "$2"; done', "loop", join(scripts, "tlc-matrix.sh"), join(dir, "One.matrix")], {
      detached: true,
      env: { ...process.env, JAVA: java, TLC_JAR: join(dir, "tools.jar"), TASK_STARTS: starts, FORMAL_MIN_FREE_GIB: "0" },
    });
    const timer = setInterval(() => {
      if (existsSync(starts) && readFileSync(starts, "utf8").endsWith("\n")) {
        clearInterval(timer);
        process.kill(-child.pid, "SIGINT");
      }
    }, 20);
    const guard = setTimeout(() => {
      try {
        process.kill(-child.pid, "SIGKILL");
      } catch {
        // The loop already ended.
      }
    }, 10000);
    child.on("close", (exitCode, signalName) => {
      clearInterval(timer);
      clearTimeout(guard);
      resolve({ exitCode, signalName });
    });
  });
  assert.equal(readFileSync(starts, "utf8"), "start\n");
  assert.equal(result.signalName, "SIGINT", JSON.stringify(result));
});

test("SIGTERM, SIGHUP and SIGKILL sent to the runner process group still stop TLC", async () => {
  for (const sig of ["SIGTERM", "SIGHUP", "SIGKILL"]) {
    const dir = fixture();
    writeFileSync(join(dir, "One.tla"), "---- MODULE One ----\n====\n");
    writeFileSync(join(dir, "One.matrix"), "spec One.tla\nrun hang | N=1\n");
    writeFileSync(join(dir, "tools.jar"), "user supplied");
    const pidFile = join(dir, "child.pid");
    const java = fakeTlc(dir, 'echo "$$" > "$TASK_PID_FILE"\nexec sleep 30');
    await new Promise((resolve) => {
      const child = spawn("bash", [join(scripts, "tlc-matrix.sh"), join(dir, "One.matrix")], {
        detached: true,
        env: { ...process.env, JAVA: java, TLC_JAR: join(dir, "tools.jar"), TASK_PID_FILE: pidFile, FORMAL_MIN_FREE_GIB: "0" },
      });
      const timer = setInterval(() => {
        if (existsSync(pidFile) && readFileSync(pidFile, "utf8").endsWith("\n")) {
          clearInterval(timer);
          process.kill(-child.pid, sig);
        }
      }, 20);
      child.on("close", () => {
        clearInterval(timer);
        resolve();
      });
    });
    const pid = Number(readFileSync(pidFile, "utf8").trim());
    assertProcessStopped(pid);
  }
});

test("signal_cleanup preserves an already ignored SIGINT", () => {
  const script = [
    "import os, signal, sys",
    `sys.path.insert(0, ${JSON.stringify(scripts)})`,
    "import workdir",
    "signal.signal(signal.SIGINT, signal.SIG_IGN)",
    "with workdir.signal_cleanup():",
    "    os.kill(os.getpid(), signal.SIGINT)",
    "print('survived')",
  ].join("\n");
  const result = spawnSync("python3", ["-B", "-c", script], { cwd: root, encoding: "utf8" });
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout.trim(), "survived");
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

test("lean-check.sh honors TMPDIR, and on SIGTERM stops its build and the processes it started, cleans its temp dir and ends by SIGTERM", async () => {
  const dir = fixture();
  const project = join(dir, "lean");
  const leanTmp = join(dir, "lean-tmp");
  writeLeanProject(project);
  writeFileSync(join(project, "Model.lean"), "def x : Nat := 1\n");
  const readyFile = join(dir, "elan.ready");
  command(dir, "elan", [
    '[ "$4" = "--version" ] && exit 0',
    'sleep 15 &',
    'echo "$$ $!" > "$TASK_READY_FILE"',
    'wait',
  ].join("\n"));
  const start = Date.now();
  const code = await new Promise((resolve) => {
    const child = spawn("bash", [join(scripts, "lean-check.sh"), project], {
      env: { ...process.env, PATH: join(dir, "bin") + ":" + process.env.PATH, TMPDIR: leanTmp, TASK_READY_FILE: readyFile, FORMAL_MIN_FREE_GIB: "0" },
    });
    const timer = setInterval(() => {
      if (existsSync(readyFile) && readFileSync(readyFile, "utf8").endsWith("\n")) {
        clearInterval(timer);
        child.kill("SIGTERM");
      }
    }, 20);
    child.on("close", (exitCode, signalName) => {
      clearInterval(timer);
      resolve({ exitCode, signalName });
    });
  });
  assert.ok(Date.now() - start < 4000, "lean-check.sh waited for child instead of exiting promptly on SIGTERM");
  for (const pid of readFileSync(readyFile, "utf8").trim().split(" ")) assertProcessStopped(Number(pid));
  assert.deepEqual(readdirSync(leanTmp), []);
  assert.equal(code.signalName, "SIGTERM", JSON.stringify(code));
});
