#!/bin/bash
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
# Real Kani regressions for crate copies with local dependencies.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
scripts=$ROOT/skills/formal-verify/scripts
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

for layout in standalone workspace; do
  p=$work/$layout/project
  mkdir -p "$p/proof/src" "$p/logic/src" "$p/../shared/src" "$p/../optional/src"
  mkdir -p "$p/.cargo" "$p/proof/.cargo"
  printf '[env]\nAFV_WORKSPACE_CONFIG="workspace"\n' > "$p/.cargo/config.toml"
  printf 'AFV_CONFIG_FILE={value="../resource.txt", relative=true}\n' >> "$p/.cargo/config.toml"
  printf 'resource outside every copied package\n' > "$p/../resource.txt"
  printf '[env]\nAFV_CRATE_CONFIG="crate"\n' > "$p/proof/.cargo/config.toml"
  if [ "$layout" = workspace ]; then
    cat > "$p/Cargo.toml" <<'EOF'
[workspace]
members = ["proof", "logic"]
resolver = "2"
[workspace.package]
version = "0.1.0"
edition = "2021"
[workspace.dependencies]
logic = { path = "logic" }
EOF
    cat > "$p/proof/Cargo.toml" <<'EOF'
[package]
name = "proof"
version.workspace = true
edition.workspace = true
[dependencies]
logic.workspace = true
EOF
  else
    cat > "$p/proof/Cargo.toml" <<'EOF'
[package]
name = "proof"
version = "0.1.0"
edition = "2021"
[dependencies]
logic = { path = "../logic" }
EOF
  fi
  printf 'optional = { path = "../../optional", optional = true }\n' >> "$p/proof/Cargo.toml"
  cat > "$p/logic/Cargo.toml" <<'EOF'
[package]
name = "logic"
version = "0.1.0"
edition = "2021"
[dependencies]
shared = { path = "../../shared" }
EOF
  printf '[package]\nname="shared"\nversion="0.1.0"\nedition="2021"\n' > "$p/../shared/Cargo.toml"
  printf 'pub fn step(n: u8) -> u8 { n.saturating_add(1) }\n' > "$p/../shared/src/lib.rs"
  printf '[package]\nname="optional"\nversion="0.1.0"\n' > "$p/../optional/Cargo.toml"
  touch "$p/../optional/src/lib.rs"
  printf 'pub fn step(n: u8) -> u8 { shared::step(n) }\n' > "$p/logic/src/lib.rs"
  cat > "$p/proof/src/lib.rs" <<'EOF'
const _: &str = env!("AFV_WORKSPACE_CONFIG");
const _: &str = env!("AFV_CRATE_CONFIG");
const _: &str = include_str!(env!("AFV_CONFIG_FILE"));
#[cfg(kani)]
mod unrelated;
pub fn step(n: u8) -> u8 { logic::step(n) }
#[cfg(kani)]
mod proofs {
    #[kani::proof]
    #[kani::unwind(2)]
    fn increments() {
        let n: u8 = kani::any();
        kani::assume(n < 255);
        assert!(super::step(n) > n);
        kani::cover!(n == 254);
    }
}
EOF
  cat > "$p/proof/src/unrelated.rs" <<'EOF'
#[kani::proof]
#[kani::unwind(2)]
fn another_file() {
    let n: u8 = kani::any();
    kani::assume(n < 255);
    assert!(n + 1 > n);
    kani::cover!(n == 254);
}
EOF
  printf 'mutation no increment\ndetects proofs::increments\n- logic::step(n)\n+ n\n' > "$p/proof/src/lib.mutations"
  printf 'existing list report\n' > "$p/proof/kani-list.json"
  bash "$scripts/kani-check.sh" "$p/proof" > "$work/check-one" &
  first=$!
  bash "$scripts/kani-check.sh" "$p/proof" > "$work/check-two" &
  second=$!
  wait "$first"
  wait "$second"
  grep -q '^SUMMARY 2 of 2 harnesses passed$' "$work/check-one"
  grep -q '^SUMMARY 2 of 2 harnesses passed$' "$work/check-two"
  python3 "$scripts/mutate.py" "$p/proof/src/lib.mutations" | tee "$work/result"
  grep -q '^DETECTED no increment: assertion Failure:' "$work/result"
  grep -q '^SUMMARY 1 of 1 mutations detected$' "$work/result"
  grep -qF 'logic::step(n)' "$p/proof/src/lib.rs"
  grep -qx 'existing list report' "$p/proof/kani-list.json"
  if [ -f "$p/../shared/Cargo.lock" ] || [ -f "$p/../optional/Cargo.lock" ]; then
    echo 'FAIL mutation discovery wrote a lockfile into a dependency'
    exit 1
  fi
  # A second harness in this file still requires its own mutation.
  cat >> "$p/proof/src/lib.rs" <<'EOF'
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(2)]
fn same_file() {
    let n: u8 = kani::any();
    kani::assume(n < 255);
    assert!(n + 1 > n);
    kani::cover!(n == 254);
}
EOF
  if python3 "$scripts/mutate.py" "$p/proof/src/lib.mutations" > "$work/coverage"; then
    echo 'FAIL another harness in the same file was omitted from coverage'
    exit 1
  fi
  grep -q '^UNCOVERED same_file$' "$work/coverage"
  if grep -q '^UNCOVERED unrelated::' "$work/coverage"; then
    echo 'FAIL unrelated files contributed to coverage'
    exit 1
  fi
done
echo 'ok: Rust mutations preserve dependencies and Cargo config; coverage belongs to its source file'

p=$work/verdicts
mkdir -p "$p/src"
printf '[package]\nname="verdicts"\nversion="0.1.0"\nedition="2021"\n' > "$p/Cargo.toml"
cat > "$p/src/lib.rs" <<'EOF'
#[cfg(kani)]
mod proofs {
    fn external() -> u8 { panic!("must be stubbed") }
    fn replacement() -> u8 { 1 }

    #[kani::proof]
    #[kani::unwind(2)]
    #[kani::stub(external, replacement)]
    fn stubbed() {
        assert_eq!(external(), 1);
        kani::cover!(true);
    }

    #[kani::proof]
    #[kani::unwind(2)]
    fn vacuous() {
        let n: u8 = kani::any();
        kani::assume(n < 255);
        let next = n + 1;
        kani::assume(n > 10);
        kani::assume(n < 5);
        assert!(next > 0);
    }

    #[kani::proof]
    #[kani::unwind(2)]
    fn already_broken() {
        let n: u8 = kani::any();
        assert!(n == 7);
    }
}
EOF
bash "$scripts/kani-check.sh" "$p" proofs::stubbed
if bash "$scripts/kani-check.sh" "$p" proofs::vacuous > "$work/vacuous"; then
  echo 'FAIL all-unreachable harness passed'
  exit 1
fi
grep -q 'no satisfied kani::cover! witness' "$work/vacuous"
# Both harnesses use the assertion; target only the broken harness's unique block.
cat > "$p/src/lib.mutations" <<'EOF'
mutation changes an already broken harness
detects proofs::already_broken
- fn already_broken() {
-         let n: u8 = kani::any();
-         assert!(n == 7);
+ fn already_broken() {
+         let n: u8 = kani::any();
+         assert!(n == 8);
EOF
if python3 "$scripts/mutate.py" "$p/src/lib.mutations" > "$work/baseline"; then
  echo 'FAIL already broken baseline counted as detection'
  exit 1
fi
grep -q "unmutated Rust harness 'proofs::already_broken' did not pass" "$work/baseline"
if grep -q '^DETECTED ' "$work/baseline"; then
  echo 'FAIL mutation ran before its baseline passed'
  exit 1
fi
echo 'ok: Kani supports stubs and rejects vacuous harnesses and broken mutation baselines'

# Codegen must select the same standard harnesses as Kani list across Cargo targets.
python3 - "$scripts" "$work/discovery" <<'PY'
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, sys.argv[1])
import kani

work = Path(sys.argv[2]).resolve()
crate, dependency = work / "crate", work / "dependency"
for package in (crate, dependency):
    (package / "src").mkdir(parents=True)
    (package / "Cargo.toml").write_text(f'[package]\nname="{package.name}"\nversion="0.1.0"\nedition="2021"\n')
with (crate / "Cargo.toml").open("a") as manifest:
    manifest.write('[dependencies]\ndependency={path="../dependency"}\n')
for package, filename, name in [
    (crate, "src/lib.rs", "library"), (crate, "src/main.rs", "binary"),
    (crate, "src/bin/extra.rs", "extra_binary"), (crate, "tests/integration.rs", "integration"),
    (crate, "examples/demo.rs", "example"), (dependency, "src/lib.rs", "dependency"),
]:
    source = package / filename
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(f'#[cfg(kani)]\n#[kani::proof]\n#[kani::unwind(2)]\nfn {name}() {{ kani::cover!(true); }}\nfn main() {{}}\n')
verifier = kani.Kani()
listed = verifier.run("--manifest-path", str(crate / "Cargo.toml"), "--target-dir", str(work / "list-target"),
                      "list", "--format", "json", cwd=crate)
assert listed.returncode == 0, listed.stdout + listed.stderr
report = json.loads((crate / "kani-list.json").read_text())
expected = {name for names in report["standard-harnesses"].values() for name in names}
assert expected == {"library", "binary", "extra_binary"}, expected
assert set(kani.discover(crate, work / "codegen", verifier)) == expected
print("ok: codegen discovery preserves standard harnesses across targets and dependencies")
PY
