#!/bin/bash
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
# Builds a Lean 4 model with Lake, then audits every declaration of every built
# module. Fails when the build fails, a declaration uses sorry or rests on an
# axiom beyond propext, Classical.choice and Quot.sound, no Lake library owns a
# .lean file in the project, a theorem named <Property>.witness does not state
# that the hypotheses of <Property> hold together, or the pin's leanchecker
# rejects a built module on kernel replay. Otherwise prints the build output,
# a WITNESS line for each public theorem and PASS. A property without a witness
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

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
log=$work/build.log
command -v python3 > /dev/null || { echo "UNAVAILABLE python3 is required to check frozen Lean statements; install Python 3"; exit 3; }
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
elan run "$toolchain" lake --dir "$dir" query "${sources[@]/%/:olean}" > "$work/oleans" 2> "$log"
status=$?
# Lean quotes sorry with backticks or straight quotes depending on the version.
sorry='^(warning|error): .*: declaration uses .sorry.'
sorries=$(grep -cE "$sorry" "$log")

# The audit imports those modules and collects the axioms under each of their
# declarations, so it needs no #print axioms line in the model. It skips the
# compiler's auxiliary declarations, which older pins store with opaque
# placeholders that would read as axioms.
audit_status=0
: > "$work/audit.out"
if [ "$status" -eq 0 ]; then
  # The module of each source, in source order, for the audit's imports and the frozen records.
  unexpected=$(grep -v '/\.lake/build/lib/lean/.*\.olean$' "$work/oleans")
  [ -z "$unexpected" ] || { echo "FAIL $scope: cannot identify the module of $unexpected"; exit 1; }
  sed -e 's|^.*/\.lake/build/lib/lean/||' -e 's|\.olean$||' -e 's|/|.|g' "$work/oleans" > "$work/modules"
  {
    echo "import Lean"
    sed 's|^|import |' "$work/modules"
    cat << 'EOF'
open Lean in
private def hasTheoremParent (env : Environment) : Name → Bool
  | .anonymous => false
  | .str parent _ | .num parent _ =>
    (match env.find? parent with | some (.thmInfo _) => true | _ => false) || hasTheoremParent env parent

open Lean in
private def oneLine (s : String) : String :=
  (s.foldl (fun (acc, gap) c =>
    if c.isWhitespace then (acc, true) else ((if gap then acc.push ' ' else acc).push c, false)) ("", false)).1

-- A property's hypotheses can hold together when some values of its variables
-- satisfy all of them. The witness must state exactly that, and the statement
-- is rebuilt from the property's type on every run, so it cannot go stale.
open Lean Meta in
private def witnessLine (property : ConstantInfo) (witness? : Option ConstantInfo) : MetaM String :=
  forallTelescope property.type fun xs _ => do
    let name := property.name
    let binders ← xs.mapM fun x => return (x, ← inferType x)
    let hyps ← binders.filterM fun (_, type) => isProp type
    if hyps.isEmpty then return s!"WITNESS no-hypotheses {name}"
    let proofs := hyps.map (·.1.fvarId!)
    for (x, type) in binders do
      if type.hasAnyFVar proofs.contains then
        return s!"WITNESS unavailable {name}: the type of {← ppExpr x} uses the proof of a hypothesis"
    let vars := binders.filter fun (x, _) => !proofs.contains x.fvarId!
    let all := hyps.pop.foldr (fun (_, hyp) rest => mkAnd hyp rest) hyps.back!.2
    -- Explicit binders printed with their types let the statement be copied into the model.
    let expected ← vars.foldrM (fun (x, type) body => do
      mkAppM ``Exists #[.lam (← x.fvarId!.getUserName) type (body.abstract #[x]) .default]) all
    let shown := oneLine (← withOptions (·.setBool `pp.funBinderTypes true) (ppExpr expected)).pretty
    let some witness := witness? | return s!"WITNESS absent {name}: no theorem {name}.witness states {shown}"
    let levels ← mkFreshLevelMVars property.levelParams.length
    if ← isDefEq witness.type (expected.instantiateLevelParams property.levelParams levels) then
      return s!"WITNESS checked {name}"
    return s!"WITNESS failed {name}: {name}.witness must state {shown}"

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let freezing := (← IO.getEnv "AFV_FREEZE") == some "1"
  let modules := (env.imports.map (·.module)).erase `Lean
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := env.constants.fold (fun acc name info => if info matches .axiomInfo _ then acc else acc.push name) #[]
  let mut audited := 0
  let mut theorems : Array (Name × Name × ModuleIdx) := #[]
  for name in names do
    let some idx := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[idx.toNat]! do continue
    if ((privateToUserName? name).getD name).isInternal then continue
    audited := audited + 1
    let extra := (← collectAxioms name).filter (!standard.contains ·)
    let extra := if freezing then extra.filter (· != ``sorryAx) else extra
    unless extra.isEmpty do IO.println s!"AXIOMS '{name}' depends on axioms: {extra}"
    let userName := (privateToUserName? name).getD name
    if userName.isInternalDetail && hasTheoremParent env name && (← findDeclarationRanges? name).isNone then continue
    let info := (env.find? name).get!
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
      | .axiomInfo _ => "axiom"
    let value := match info with
      | .defnInfo v => toJson (reprStr v.value)
      | _ => Json.null
    let pp ← liftTermElabM <| Meta.ppExpr info.type
    let record := Json.mkObj [
      ("module", toJson env.header.moduleNames[idx.toNat]!.toString),
      ("name", toJson userName.toString), ("kind", toJson kind),
      ("typeExpr", toJson (reprStr (info.levelParams, info.type))),
      ("valueExpr", value), ("type", toJson pp.pretty)]
    IO.println s!"STATEMENT {record.compress}"
    if info matches .thmInfo _ then theorems := theorems.push (name, userName, idx)
  -- A property is a theorem the mutation runner would target: public, written
  -- in the source, and neither a projection nor an instance.
  for (name, userName, idx) in theorems.qsort (·.1.toString < ·.1.toString) do
    if name != userName || userName matches .str _ "witness" then continue
    if env.isProjectionFn name || Meta.isInstanceCore env name then continue
    if (← findDeclarationRanges? name).isNone then continue
    let witness? := theorems.find? fun (_, user, owner) => owner == idx && user == userName ++ `witness
    let line ← liftTermElabM <| tryCatchRuntimeEx
      (witnessLine (env.find? name).get! (witness?.bind (env.find? ·.1)))
      fun error => return s!"WITNESS unavailable {name}: {oneLine (← error.toMessageData.toString)}"
    IO.println line
  IO.println s!"AUDITED {audited} declarations"
EOF
  } > "$work/Audit.lean"
  AFV_FREEZE=$freeze elan run "$toolchain" lake --dir "$dir" env lean "$work/Audit.lean" > "$work/audit.out" 2>&1
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
    grep -v '^[[:space:]]*$' "$work/audit.out" | tail -40
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
# through the kernel and rejects it. It reads each argument as a name prefix,
# so the count comes from the modules it lists, not from the arguments.
replay=unavailable
if [ -x "$(elan run "$toolchain" lean --print-prefix)/bin/leanchecker" ]; then
  modules=()
  while IFS= read -r module; do modules+=("$module"); done < "$work/modules"
  replay=passed
  elan run "$toolchain" lake --dir "$dir" env leanchecker -v "${modules[@]}" > "$work/replay.out" 2>&1 || replay=failed
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
