#!/bin/bash
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
scripts=$ROOT/skills/formal-verify/scripts
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

missed() {
  local out
  if out=$(python3 "$scripts/mutate.py" "$work/$1.mutations"); then
    echo "FAIL an undetected mutation passed: $1"
    exit 1
  fi
  printf '%s\n' "$out"
  grep -q '^MISSED ' <<< "$out"
}

cat > "$work/Scope.tla" <<'MODEL'
---- MODULE Scope ----
CONSTANT Large
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x
Within == x = 0 \/ Large
====
MODEL
cat > "$work/Scope.mutations" <<'MUTATIONS'
mutation change initial value
detects Within
- Init == x = 0
+ Init == x = 1
MUTATIONS
cat > "$work/Scope.matrix" <<'MATRIX'
spec Scope.tla
run small | Large=FALSE
check INVARIANT Within
run large | Large=TRUE
MATRIX
missed Scope
cat > "$work/Scope.matrix" <<'MATRIX'
spec Scope.tla
check INVARIANT Within
run large | Large=TRUE
spec ./Scope.tla
run small | Large=FALSE
MATRIX
missed Scope

cat > "$work/Scope.matrix" <<'MATRIX'
spec Scope.tla
run shared small | Large=FALSE
spec ./Scope.tla
reach Within | shared
run shared large | Large=TRUE
MATRIX
cat > "$work/Scope.mutations" <<'MUTATIONS'
mutation miss the state only in the first section
detects reach:Within
- Init == x = 0
+ Init == x = 1
MUTATIONS
missed Scope

cat > "$work/Stall.tla" <<'MODEL'
---- MODULE Stall ----
VARIABLE x
Init == x = 0
Advance == x = 0 /\ x' = 1
Done == x = 1 /\ UNCHANGED x
Next == Advance \/ Done
Spec == Init /\ [][Next]_x /\ WF_x(Advance)
Arrived == <>(x = 1)
NoSkip == [][x' = 1]_x
====
MODEL
cat > "$work/Stall.matrix" <<'MATRIX'
spec Stall.tla
check PROPERTY Arrived
run default |
MATRIX
cat > "$work/Stall.mutations" <<'MUTATIONS'
mutation stop after arriving
detects Arrived
- Done == x = 1
+ Done == x = 2
MUTATIONS
missed Stall
cat > "$work/Stall.mutations" <<'MUTATIONS'
mutation stop before arriving
detects Arrived
- Advance == x = 0
+ Advance == x = 2
MUTATIONS
python3 "$scripts/mutate.py" "$work/Stall.mutations" | tee "$work/detected.out"
grep -q "^DETECTED stop before arriving: Arrived fails in run 'default' (Temporal properties were violated)$" "$work/detected.out"
cat > "$work/Stall.matrix" <<'MATRIX'
spec Stall.tla
check PROPERTY NoSkip
run default |
MATRIX
cat > "$work/Stall.mutations" <<'MUTATIONS'
mutation advance past goal
detects NoSkip
- Advance == x = 0 /\ x' = 1
+ Advance == x = 0 /\ x' = 2
MUTATIONS
python3 "$scripts/mutate.py" "$work/Stall.mutations" | tee "$work/action.out"
grep -q "^DETECTED advance past goal: NoSkip fails in run 'default' (Action property NoSkip is violated)$" "$work/action.out"
