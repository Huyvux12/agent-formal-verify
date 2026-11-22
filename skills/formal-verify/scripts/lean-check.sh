#!/bin/bash
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
# Builds a Lean 4 model with Lake, then audits every declaration of every built
# module. Fails when the build fails, a declaration uses sorry or rests on an
# axiom beyond propext, Classical.choice and Quot.sound, no Lake library owns a
# .lean file in the project, a theorem named <Property>.witness does not state
# that the hypotheses of <Property> hold together, or the pin's leanchecker
# rejects a built module on kernel replay. Otherwise prints the build output,
# a WITNESS line for each property and PASS. A property without a witness
# passes, and so does a pin that ships no leanchecker; the PASS line counts the
# first and reports the replay as unavailable for the second.
# Named files limit the check to those sources, so agents that share a project
# can each check their own model; a run without them checks the whole project.
# Needs a pin of Lean 4.20.0 or later, the first whose Lake builds a module by
# its source path.
#
# Usage: lean-check.sh <lake-project-dir> [--freeze] [<file.lean> ...]
#   A file is absolute or relative to the project.
set -uo pipefail
[ "$#" -gt 0 ] || { echo "usage: lean-check.sh <lake-project-dir> [--freeze] [<file.lean> ...]"; exit 2; }
dir=$1
shift
freeze=0
if [ "${1-}" = "--freeze" ]; then freeze=1; shift; fi
for arg; do
  [[ $arg != --* ]] || { echo "usage: --freeze must precede source files"; exit 2; }
done
HERE=$(cd "$(dirname "$0")" && pwd)
[ -f "$dir/lakefile.toml" ] || [ -f "$dir/lakefile.lean" ] || { echo "FAIL $dir has no lakefile"; exit 1; }
dir=$(cd "$dir" && pwd)
# shellcheck source=skills/formal-verify/scripts/lean-tools.sh
source "$HERE/lean-tools.sh"
toolchain=$(lean_ready_pin "$dir") || { status=$?; echo "$toolchain"; exit "$status"; }

if [ -n "${TMPDIR:-}" ]; then
  mkdir -p "$TMPDIR" || { echo "FAIL TMPDIR=$TMPDIR cannot be created"; exit 1; }
  work=$(mktemp -d "${TMPDIR%/}/lean-check.XXXXXX") || { echo "FAIL cannot create temporary directory in TMPDIR=$TMPDIR"; exit 1; }
else
  work=$(mktemp -d)
fi
trap 'rm -rf "$work"' EXIT
log=$work/build.log
# shellcheck source=skills/formal-verify/scripts/python-tools.sh
source "$HERE/python-tools.sh"
require_python || exit 3
python3 "$HERE/storage.py" warn
# Each build step runs as a background job through processes.py, so a signal's trap can stop the step and
# every process it started (elan runs lake, which runs lean) and then end the script by the same signal.
# The trap finds the step in the job table, which holds it from the moment it starts.
stop_step() {
  trap '' INT TERM HUP
  local running
  running=$(jobs -p)
  if [ -n "$running" ]; then
    kill -TERM "$running" 2> /dev/null
    wait
  fi
  rm -rf "$work"
  trap - EXIT "$1"
  kill -"$1" "$$"
}
trap 'stop_step INT' INT
trap 'stop_step TERM' TERM
trap 'stop_step HUP' HUP
run_step() {
  python3 "$HERE/processes.py" run "$@" &
  wait "$!"
}
# Lake builds a module named by its source path and rejects a path that no
# library owns, so naming every source leaves no file unchecked. Its query
# command prints the .olean of each, which names the modules to audit without
# picking up a module left in the build directory by a deleted source.
sources=()
scope=$dir
if [ "$#" -gt 0 ]; then
  scope="$dir ($* only)"
  for src; do
    [[ $src == /* ]] || src=$dir/$src
    [ -f "$src" ] || { echo "FAIL $src does not exist"; exit 1; }
    sources+=("$src")
  done
else
  if [ "$freeze" -eq 0 ]; then
    python3 "$HERE/lean-statements.py" orphans "$dir" > "$work/orphans.out"
    orphan_status=$?
    if [ "$orphan_status" -ne 0 ]; then
      echo "FAIL $scope: frozen model sources are missing or their records are invalid"
      cat "$work/orphans.out"
      exit "$orphan_status"
    fi
  fi
  while IFS= read -r src; do sources+=("$src"); done \
    < <(find "$dir" -name '*.lean' -not -path "$dir/.lake/*" -not -name lakefile.lean | sort)
  [ "${#sources[@]}" -gt 0 ] || { echo "FAIL $dir has no .lean file to check"; exit 1; }
fi
run_step elan run "$toolchain" lake --dir "$dir" query "${sources[@]/%/:olean}" > "$work/oleans" 2> "$log"
status=$?
# Lean quotes sorry with backticks or straight quotes depending on the version.
sorry='^(warning|error): .*: declaration uses .sorry.'
sorries=$(grep -cE "$sorry" "$log")

# lean-analysis.lean audit imports those modules and collects the axioms under each of their
# declarations, so it needs no #print axioms line in the model. It skips the
# compiler's auxiliary declarations, which older pins store with opaque
# placeholders that would read as axioms.
audit_status=0
: > "$work/audit.out"
if [ "$status" -eq 0 ]; then
  # The module of each source, in source order, for the audit's imports and the frozen records.
  if ! run_step elan run "$toolchain" lake --dir "$dir" env python3 "$HERE/lean-layout.py" \
      "$work/oleans" "$work/modules" "$work/libraries" > "$work/layout.log" 2>&1; then
    echo "FAIL $scope: cannot resolve Lake's module layout"
    cat "$work/layout.log"
    exit 1
  fi
  audit=(audit "$work/modules")
  [ "$freeze" -eq 0 ] || audit=(audit --freeze "$work/modules")
  run_step elan run "$toolchain" lake --dir "$dir" env lean --run "$HERE/lean-analysis.lean" "${audit[@]}" > "$work/audit.out" 2>&1
  audit_status=$?
  grep -qE '^AUDITED [0-9]+ declarations$' "$work/audit.out" || audit_status=1
  if grep -q '^AUDITED 0 declarations$' "$work/audit.out"; then
    frozen=0
    for src in "${sources[@]}"; do
      [ ! -f "${src%.lean}.statements" ] || frozen=1
    done
    [ "$freeze" -eq 0 ] && [ "$frozen" -eq 1 ] || audit_status=1
  fi
fi
axioms=$(grep -c '^AXIOMS ' "$work/audit.out")

if [ "$status" -ne 0 ] || { [ "$freeze" -eq 0 ] && [ "$sorries" -ne 0 ]; } || [ "$axioms" -ne 0 ] || [ "$audit_status" -ne 0 ]; then
  echo "FAIL $scope: $sorries unfinished proofs (sorry), $axioms declarations on an added axiom, lake exit $status"
  grep -E "$sorry" "$log"
  grep '^AXIOMS ' "$work/audit.out"
  [ "$status" -eq 0 ] || grep -v '^[[:space:]]*$' "$log" | tail -40
  ! grep -q '^error: unknown module source path' "$log" \
    || echo "no library owns that file; import it from a built module or move it out of the project"
  ! grep -qE "^error: (unknown command 'query'|invalid script spec)" "$log" \
    || echo "$toolchain cannot build a module by its source path; pin Lean 4.20.0 or later"
  if [ "$audit_status" -ne 0 ]; then
    echo "the axiom audit did not run or found no declarations:"
    grep -v -e '^[[:space:]]*$' -e '^IMPORTED ' "$work/audit.out" | tail -40
    ! grep -q 'environment already contains' "$work/audit.out" \
      || echo "two modules declare the same name; put each model in a namespace of its own"
  fi
  exit 1
fi
mode=check
[ "$freeze" -eq 0 ] || mode=freeze
python3 "$HERE/lean-statements.py" "$mode" "$toolchain" "$work/audit.out" "$work/modules" "${sources[@]}" > "$work/statements.out"
statement_status=$?
if [ "$statement_status" -ne 0 ]; then
  echo "FAIL $scope: frozen statements differ or could not be checked"
  cat "$work/statements.out"
  exit "$statement_status"
fi
cat "$work/statements.out"
# #eval output arrives as info blocks that can span lines.
grep -v '^[[:space:]]*$' "$log"
[ "$freeze" -eq 0 ] || exit 0

witnesses() { grep -c "^WITNESS $1 " "$work/audit.out"; }
failed=$(witnesses failed)
[ "$failed" -eq 0 ] || echo "FAIL $scope: $failed witnesses do not state their property's hypotheses"
grep '^WITNESS ' "$work/audit.out"
[ "$failed" -eq 0 ] || exit 1

# The build trusts a declaration that a command adds to the environment without
# a kernel check. leanchecker replays every declaration of the built modules
# through the kernel and rejects it. Use its exact-module replayer rather than
# its CLI's prefix search, which also finds deleted sources' cached objects.
# A named module rests on the project modules it imports, so replay those too.
replay=unavailable
if [ -x "$(elan run "$toolchain" lean --print-prefix)/bin/leanchecker" ]; then
  cp "$work/modules" "$work/replay-modules"
  while IFS= read -r module; do
    while IFS= read -r library; do
      if [ -f "$library/${module//.//}.olean" ]; then
        printf '%s\n' "$module" >> "$work/replay-modules"
        break
      fi
    done < "$work/libraries"
  done < <(sed -n 's/^IMPORTED //p' "$work/audit.out")
  sort -u "$work/replay-modules" -o "$work/replay-modules"
  replay=passed
  AFV_REPLAY_MODULES="$work/replay-modules" run_step elan run "$toolchain" lake --dir "$dir" env lean "$HERE/lean-replay.lean" > "$work/replay.out" 2>&1 || replay=failed
fi
case $replay in
  passed) echo "REPLAYED $(grep -c '^replaying ' "$work/replay.out") modules through the Lean kernel" ;;
  failed)
    echo "FAIL $scope: kernel replay rejected a built module"
    cat "$work/replay.out"
    exit 1 ;;
  unavailable) echo "UNAVAILABLE kernel replay: $toolchain ships no leanchecker" ;;
esac
echo "PASS $scope: $(grep '^AUDITED ' "$work/audit.out" | cut -d' ' -f2) declarations checked, no unfinished proof (sorry), no added axiom, kernel replay $replay, $(witnesses checked) witnesses checked, $(witnesses absent) absent, $(witnesses unavailable) unavailable, $(witnesses no-hypotheses) properties without hypotheses"
