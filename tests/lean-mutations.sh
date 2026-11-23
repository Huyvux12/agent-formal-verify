#!/bin/bash
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
# Real Lean regressions for declaration discovery and proof-sensitivity reporting.
# Optionally pass an installed toolchain pin to exercise an older supported Lean.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
scripts=$ROOT/skills/formal-verify/scripts
work=$(mktemp -d)
work=$(cd "$work" && pwd -P)
trap 'rm -rf "$work"' EXIT
# shellcheck source=tests/lib.sh
source "$ROOT/tests/lib.sh"
lean_project "$work"
if [ "$#" -gt 0 ]; then printf '%s\n' "$1" > "$work/lean-toolchain"; fi

cat > "$work/Model/Step.lean" <<'EOF'
namespace Step
def step (n : Nat) : Nat := n + 1
namespace Live
  @[simp] theorem property (n : Nat) : n < step n := by simp [step]
end Live
namespace Vacuous
  theorem property (n : Nat) (h : n < 0) : n < step n := absurd h (Nat.not_lt_zero n)
end Vacuous
private theorem helper : True := trivial
end Step
EOF
printf 'mutation no increment\n- n + 1\n+ n\n' > "$work/Model/Step.mutations"
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean
bash "$scripts/lean-check.sh" "$work"
# An indented vacuous theorem that shares its name with another must not escape coverage.
rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -q '^DETECTED no increment: proof/check fails: theorem Step.Live.property$' "$work/result"
grep -q '^UNCOVERED theorem Step.Vacuous.property$' "$work/result"
if grep -q '^UNCOVERED theorem Step.helper$' "$work/result"; then
  echo 'FAIL private helper counted as a coverage target'
  exit 1
fi

# A mutation that edits only a theorem's own proof does not cover that theorem.
printf 'mutation edit the vacuous proof only\n- absurd h (Nat.not_lt_zero n)\n+ absurd h (Nat.lt_irrefl n)\n' > "$work/Model/Step.mutations"
rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -q '^theorem Step.Vacuous.property: the mutation edits this theorem' "$work/result"
printf 'mutation no increment\n- n + 1\n+ n\n' > "$work/Model/Step.mutations"

# Removing a frozen theorem must not turn incomplete mutation coverage green.
sed -i.orig '/(h : n < 0)/d' "$work/Model/Step.lean"
rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
grep -Fq 'FROZEN Step.Vacuous.property: statement changed' "$work/result"
# A malformed freeze record allows no mutation credit.
printf '{"declarations":[]}\n' > "$work/Model/Step.statements"
rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
grep -q 'unsupported statements format' "$work/result"

# Proposition-valued projections and instances are not property declarations.
# A theorem with an anonymous instance binder keeps its statement when the
# mutation shifts the hygiene numbers that Lean 4.20 gives such binders.
cat > "$work/Model/Step.lean" <<'EOF'
namespace Step
def step (n : Nat) : Nat := n + 1
theorem property (n : Nat) : n < step n := by simp [step]
private theorem premises_hold : ∃ n : Nat, 0 < n := ⟨1, by decide⟩
example : ∃ n : Nat, 0 < n := ⟨1, by decide⟩
structure Pos where
  n : Nat
  pos : 0 < n
class Good (n : Nat) : Prop where
  ok : 0 < n
theorem good (n : Nat) [Good n] : n < step n := by simp [step]
instance globalGood : Good 1 := ⟨by decide⟩
section
local instance localGood : Good 2 := ⟨by decide⟩
end
namespace Scoped
scoped instance scopedGood : Good 3 := ⟨by decide⟩
end Scoped
end Step
EOF
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean
python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -q '^DETECTED no increment: proof/check fails: theorem Step.property; theorem Step.good$' "$work/result"
if grep -q '^UNCOVERED' "$work/result"; then
  echo 'FAIL projection or instance counted as a coverage target'
  exit 1
fi

# Option and section-variable wrappers must preserve guard attribution.
cat > "$work/Model/Step.lean" <<'EOF'
namespace Step
def step (n : Nat) : Nat := n + 1
set_option maxRecDepth 2048 in
#guard step 0 == 1
set_option maxRecDepth 2048 in
set_option maxHeartbeats 400000 in
#guard step 0 == 1
variable (n : Nat) in
#guard step 0 == 1
end Step
EOF
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean
python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -q '^SUMMARY 1 of 1 mutations detected$' "$work/result"
grep -Fqx "DETECTED no increment: proof/check fails: #guard at $work/Model/Step.lean:4; #guard at $work/Model/Step.lean:7; #guard at $work/Model/Step.lean:9" "$work/result"

# Errors in a wrapper must not be attributed to the check it contains.
printf 'mutation invalid option\n- set_option maxRecDepth 2048 in\n- #guard step 0 == 1\n+ set_option maxRecDepth true in\n+ #guard step 0 == 1\n' > "$work/Model/Step.mutations"
rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -q "^FAIL mutation 'invalid option' did not reach a verdict:" "$work/result"
printf 'mutation no increment\n- n + 1\n+ n\n' > "$work/Model/Step.mutations"

# Proof sensitivity alone cannot establish non-vacuity. The same statement
# remains provable on the mutant by using its contradictory hypothesis.
cat > "$work/Model/Step.lean" <<'EOF'
namespace Step
def step (n : Nat) : Nat := n + 1
theorem vacuous (n : Nat) (_h : n < 0) : n < step n := by simp [step]
end Step
EOF
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean
python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -q '^DETECTED no increment: proof/check fails: theorem Step.vacuous$' "$work/result"
grep -q '^NOTE Lean detections mean existing proofs fail, not that theorem statements are false or hypotheses satisfiable\.$' "$work/result"
cat > "$work/Model/Step.lean" <<'EOF'
namespace Step
def step (n : Nat) : Nat := n
theorem vacuous (n : Nat) (h : n < 0) : n < step n := absurd h (Nat.not_lt_zero n)
end Step
EOF
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean
bash "$scripts/lean-check.sh" "$work"

cat > "$work/Model/Step.lean" <<'EOF'
namespace Step
def step (n : Nat) : Nat := n + 1
theorem property (n : Nat) : n < step n := by simp [step]
example : step 0 = 1 := by rfl
#guard step 0 == 1
section
variable (k : Nat)
example : k < step k := by simp [step]
end
example (n : Nat) [NeZero n] : 0 < step n := by simp [step]
end Step
EOF
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean
printf 'mutation no increment\n- n + 1\n+ n\n+ -- extra line\n' > "$work/Model/Step.mutations"
python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -Fqx "DETECTED no increment: proof/check fails: theorem Step.property; example at $work/Model/Step.lean:4; #guard at $work/Model/Step.lean:5; example at $work/Model/Step.lean:8; example at $work/Model/Step.lean:10" "$work/result"

# A syntax error in a definition must never count as a detected bug.
printf 'mutation invalid definition\n- n + 1\n+ n +\n' > "$work/Model/Step.mutations"
rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -q "^FAIL mutation 'invalid definition' did not reach a verdict:" "$work/result"
if grep -q '^DETECTED' "$work/result"; then
  echo 'FAIL invalid definition reported as a detected mutation'
  exit 1
fi

# A mutation that changes a theorem's statement must never count as a proof
# failure, whether the statement stops elaborating or Lean binds the renamed
# definition as an automatic implicit variable so that only the proof fails.
printf 'mutation rename step\n- def step (n : Nat)\n+ def step2 (n : Nat)\n' > "$work/Model/Step.mutations"
for theorem in 'property (n : Nat) : n < step n := by simp [step]' \
  'unapplied (f : Nat → Nat) (h : f = step) : f 0 = 1 := by subst h; rfl'; do
  printf 'namespace Step\ndef step (n : Nat) : Nat := n + 1\ntheorem %s\nend Step\n' "$theorem" > "$work/Model/Step.lean"
  bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean
  rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
  cat "$work/result"
  grep -q "^FAIL mutation 'rename step' did not reach a verdict:" "$work/result"
  grep -q "^theorem Step.${theorem%% *}: the mutation changes its statement" "$work/result"
done

# The same holds for an example or #guard, which has no declaration to compare.
for check in 'example : step 0 = 1 := by rfl' \
  'example (f : Nat → Nat) (h : f = step) : f 0 = 1 := by subst h; rfl' \
  '#guard step 0 == 1'; do
  printf 'namespace Step\ndef step (n : Nat) : Nat := n + 1\n%s\nend Step\n' "$check" > "$work/Model/Step.lean"
  bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean
  rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
  cat "$work/result"
  grep -q "^FAIL mutation 'rename step' did not reach a verdict:" "$work/result"
  grep -Fq "${check%% *} at $work/Model/Step.lean:3: the mutation changes its statement" "$work/result"
done

# A new example that repeats an existing example's statement cannot count as a detection.
printf 'def one : Nat := 1\nexample : True := trivial\n' > "$work/Model/Step.lean"
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean
for edit in \
  $'- def one : Nat := 1\n+ def one : Nat := 1\n+ example : True := by exact 0' \
  $'- trivial\n+ by exact 0\n+ example : True := trivial'; do
  printf 'mutation insert duplicate example\n%s\n' "$edit" > "$work/Model/Step.mutations"
  rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
  grep -q "^FAIL mutation 'insert duplicate example' did not reach a verdict:" "$work/result"
  grep -Fq 'cannot match this example to a single original check' "$work/result"
done

# A mutation that breaks only a witness is missed, and a public witness is no coverage target.
cat > "$work/Model/Step.lean" <<'EOF'
namespace Step
def step (n : Nat) : Option Nat := if n < 3 then some (n + 1) else none
theorem bounded (n m : Nat) (h : step n = some m) : m ≤ 4 := by
  unfold step at h
  split at h <;> simp_all <;> omega
theorem bounded.witness : ∃ (n : Nat), ∃ (m : Nat), step n = some m := ⟨0, 1, rfl⟩
theorem witness (n : Nat) (h : n < 3) : n < 4 := by omega
end Step
EOF
printf 'mutation never step\n- if n < 3 then\n+ if n < 0 then\n' > "$work/Model/Step.mutations"
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean
bash "$scripts/lean-check.sh" "$work" | tee "$work/check"
grep -q '^WITNESS absent Step.witness: ' "$work/check"
rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -q '^MISSED never step$' "$work/result"
if grep -q '^UNCOVERED theorem Step.bounded.witness$' "$work/result"; then
  echo 'FAIL a public witness counted as a coverage target'
  exit 1
fi
grep -q '^UNCOVERED theorem Step.witness$' "$work/result"

# Lean 4.20 numbers hygienic names and abstracted proofs across the whole module,
# so declarations added above frozen ones must leave their records alone, while an
# edit to a frozen body still fails. Deriving and an enumeration add hygienic names.
frozen_double() {
  {
    echo 'namespace Step'
    cat
    echo 'def double : Nat → Nat'
    echo '  | 0 => 0'
    echo "  | n + 1 => double n + $1"
    echo 'structure Pair where'
    echo '  a : Nat'
    echo 'deriving BEq, Repr'
    echo 'inductive Color | red | green'
    echo 'end Step'
  } > "$work/Model/Step.lean"
}
frozen_double 2 < /dev/null
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean > /dev/null
above='def pick (n : Nat) : Nat := match n with | 0 => 1 | _ => 2
theorem pick_pos (n : Nat) : 0 < pick n := by unfold pick; split <;> decide'
frozen_double 2 <<< "$above"
bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check" || { cat "$work/check"; echo 'FAIL declarations added above a frozen definition changed its record'; exit 1; }
frozen_double 3 <<< "$above"
rejected bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check"
grep -q '^  definition value changed$' "$work/check"

# A constant that a macro defines has a hygienic name and no record of its own, so a frozen
# definition that uses it records the constant's content as well: here a helper with a proof,
# whose abstracted proof Lean 4.20 numbers module-wide, and a partial helper, whose body sits
# in its _unsafe_rec auxiliary.
frozen_helper() {
  {
    echo 'namespace Step'
    echo 'macro "defWithHelper " n:ident " := " v:term ", " w:term : command =>'
    # shellcheck disable=SC2016 # Lean text, not shell expansions.
    echo '  `(def helper : {k : Nat // 0 < k} := ⟨$v, by decide⟩'
    # shellcheck disable=SC2016
    echo '    partial def spin (k : Nat) : Nat := if k = 0 then $w else spin (k - 1)'
    # shellcheck disable=SC2016
    echo '    def $n (k : Nat) : Nat := helper.val + spin k)'
    cat
    echo "defWithHelper f := 1, $1"
    echo 'end Step'
  } > "$work/Model/Step.lean"
}
frozen_helper 1 < /dev/null
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean > /dev/null
frozen_helper 1 <<< 'def proved : {k : Nat // 0 < k} := ⟨2, by decide⟩
defWithHelper g := 5, 6'
bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check" || { cat "$work/check"; echo 'FAIL a declaration added above changed the record of a definition that uses a hygienic constant'; exit 1; }
frozen_helper 2 < /dev/null
rejected bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check"
grep -q '^FROZEN Step.f: statement changed$' "$work/check"

# Lean shares one match helper among the matches of the same shape in a module, and a pattern
# lambda and a recursive definition elaborate through one, so a match added above a frozen
# definition must leave its record alone, while an edit to the frozen definition's own match
# still fails. Lean 4.20 also names a recursive definition's binders after the shared helper.
frozen_match() {
  {
    echo 'namespace Step'
    cat
    echo "def pick (n : Nat) : Nat := match n with | 0 => 1 | _ => $1"
    echo 'def swap : Nat × Nat → Nat × Nat := fun (a, b) => (b, a)'
    echo 'def count : Nat → Nat'
    echo '  | 0 => 0'
    echo '  | k + 1 => count k'
    echo 'end Step'
  } > "$work/Model/Step.lean"
}
frozen_match 2 < /dev/null
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean > /dev/null
frozen_match 2 <<< 'def other (n : Nat) : Nat := match n with | 0 => 3 | _ => 4
def first : Nat × Nat → Nat := fun (a, _) => a
def down : Nat → Nat
  | 0 => 0
  | m + 1 => down m'
bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check" || { cat "$work/check"; echo 'FAIL a match of the same shape added above changed a frozen record'; exit 1; }
frozen_match 3 < /dev/null
rejected bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check"
grep -q '^FROZEN Step.pick: statement changed$' "$work/check"

# A record also keeps which match helper sits at each place: in a theorem's statement, in a definition's
# value, and in a hygienic constant that a frozen definition uses. Here a notation's match and the first
# match share one helper; the edit gives the notation the second match's helper, and every proof still holds.
frozen_places() {
  cat > "$work/Model/Step.lean" <<EOF
namespace Step
local notation "M3" => (match 3 with | 0 => 1 | $1)
theorem t : (match 3 with | 0 => 1 | k + 1 => k) = 2 ∧ (match 3 with | 0 => 1 | k => k) = 3 ∧ M3 = M3 := by
  decide
def v : Nat × Nat × Nat := ((match 3 with | 0 => 1 | k + 1 => k), (match 3 with | 0 => 1 | k => k), M3)
macro "defTriple " n:ident " := " w:term : command =>
  \`(def helper : Nat × Nat × Nat := ((match 3 with | 0 => 1 | k + 1 => k), (match 3 with | 0 => 1 | k => k), \$w)
    def \$n : Nat × Nat × Nat := helper)
defTriple f := M3
end Step
EOF
}
frozen_places 'k + 1 => k'
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean > /dev/null
frozen_places 'k => k'
rejected bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check"
grep -q '^FROZEN Step.t: statement changed$' "$work/check"
grep -q '^FROZEN Step.v: statement changed$' "$work/check"
grep -q '^FROZEN Step.f: statement changed$' "$work/check"

# A record also keeps which of two constants it shows alike sits at each place: two macro-made `a`s, whose
# names differ only in their macro scopes, in r, and a macro-made `a` and the user's own `a` in s. The edit
# swaps one for the other in both. A declaration added above, which renumbers the scopes, changes neither record.
frozen_same() {
  cat > "$work/Model/Step.lean" <<EOF
namespace Step
macro "inner " n:ident x:ident : command => \`(def a : Nat := 2
  def \$n : Nat := \$x + a + $1)
macro "outer " n:ident : command => \`(def a : Nat := 1
  inner \$n a)
$(cat)
outer r
def a : Nat := 1
inner s a
end Step
EOF
}
# shellcheck disable=SC2016 # Lean text, not shell expansions.
frozen_same '$x' < /dev/null
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean > /dev/null
# shellcheck disable=SC2016
frozen_same '$x' <<< 'outer q'
bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check" || { cat "$work/check"; echo 'FAIL a declaration added above changed the record of a definition that uses two constants shown alike'; exit 1; }
frozen_same a < /dev/null
rejected bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check"
grep -q '^FROZEN Step.r: statement changed$' "$work/check"
grep -q '^FROZEN Step.s: statement changed$' "$work/check"

# It keeps which of two universe parameters it shows alike sits at each place too: a macro-made `u` and the
# user's own `u`. The edit swaps them in f's type, so f.{0, 1} takes other arguments. A declaration added
# above, which renumbers the scopes, changes no record.
frozen_levels() {
  cat > "$work/Model/Step.lean" <<EOF
namespace Step
macro "mk " n:ident v:ident : command => \`(def \$n.{\$v, u} (α : Sort $1) (β : Sort ($2 + 1)) : Type (max \$v u) := PProd (PLift α) β)
$(cat)
mk f u
end Step
EOF
}
# shellcheck disable=SC2016 # Lean text, not shell expansions.
frozen_levels '$v' u < /dev/null
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean > /dev/null
# shellcheck disable=SC2016
frozen_levels '$v' u <<< 'def above : Nat := 1'
bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check" || { cat "$work/check"; echo 'FAIL a declaration added above changed the record of a definition with two universe parameters shown alike'; exit 1; }
# shellcheck disable=SC2016
frozen_levels u '$v' < /dev/null
rejected bash "$scripts/lean-check.sh" "$work" Model/Step.lean > "$work/check"
grep -q '^FROZEN Step.f: statement changed$' "$work/check"

# The mutation runner and the frozen record share one notion of a statement. A theorem that states a
# match of the same shape as a definition's shares that definition's match helper, and a mutation that
# changes the definition's match gives the theorem a helper of its own. The theorem's statement is
# unchanged, so its failing proof detects the mutation.
cat > "$work/Model/Step.lean" <<'EOF'
namespace Step
def f (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => k
theorem t (n : Nat) : (match n with | 0 => 1 | k + 1 => k) = f n := by
  cases n <;> rfl
end Step
EOF
printf 'mutation f gains an arm\n-   | k + 1 => k\n+   | 1 => 0\n+   | k + 2 => k + 1\n' > "$work/Model/Step.mutations"
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean > /dev/null
python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result" || { cat "$work/result"; echo 'FAIL a shared match helper made an unchanged theorem statement read as changed'; exit 1; }
grep -q '^DETECTED f gains an arm: proof/check fails: theorem Step.t$' "$work/result"

# The same notion keeps which match helper sits at each place in a statement. Here a notation's match
# and the theorem's first match share one helper; the mutation gives the notation the helper of the
# second match, which makes the statement false. Its failing proof shows nothing, so it gets no verdict.
cat > "$work/Model/Step.lean" <<'EOF'
namespace Step
local notation "M3" => (match 3 with | 0 => 1 | k + 1 => k)
theorem t : (match 3 with | 0 => 1 | k + 1 => k) = 2 ∧ (match 3 with | 0 => 1 | k => k) = 3 ∧ M3 = 2 := by
  decide
end Step
EOF
printf 'mutation M3 matches every k\n- local notation "M3" => (match 3 with | 0 => 1 | k + 1 => k)\n+ local notation "M3" => (match 3 with | 0 => 1 | k => k)\n' > "$work/Model/Step.mutations"
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean > /dev/null
rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -q '^theorem Step.t: the mutation changes its statement' "$work/result"

# It also keeps which of two macro-made `a`s sits at each place in a statement. The mutation swaps one
# for the other, which makes the statement false, so its failing proof gets no verdict.
cat > "$work/Model/Step.lean" <<'EOF'
namespace Step
macro "inner " n:ident x:ident : command => `(def a : Nat := 2
  theorem $n : $x + a + $x = 4 := rfl)
macro "outer " n:ident : command => `(def a : Nat := 1
  inner $n a)
outer t
end Step
EOF
# shellcheck disable=SC2016 # Lean text, not shell expansions.
printf 'mutation swap the last a\n-   theorem $n : $x + a + $x = 4 := rfl)\n+   theorem $n : $x + a + a = 4 := rfl)\n' > "$work/Model/Step.mutations"
bash "$scripts/lean-check.sh" "$work" --freeze Model/Step.lean > /dev/null
rejected python3 "$scripts/mutate.py" "$work/Model/Step.mutations" > "$work/result"
cat "$work/result"
grep -q '^theorem Step.t: the mutation changes its statement' "$work/result"
echo 'ok: qualified coverage and proof-sensitivity reporting checked with real Lean'
