-- Copyright (c) 2026 Michael Denyer
-- SPDX-License-Identifier: GPL-3.0-only
-- Read Lean's own record of a model, through the target project's pinned Lake environment.
--   audit [--freeze] <module-list>  import the built modules and print a record of each declaration
--                                   (STATEMENT), any added axiom (AXIOMS), each property's witness
--                                   check (WITNESS) and the count (AUDITED), for lean-check.sh
--   analyze <source.lean>           elaborate one source without building it and print its declarations,
--                                   checks and errors as one AFV_LEAN JSON line, for the mutation runner
-- Both describe a statement in the same position-free form, so a frozen record and a mutation agree on
-- whether a statement changed.
import Lean

open Lean in
private def hasTheoremParent (env : Environment) : Name → Bool
  | .anonymous => false
  | .str parent _ | .num parent _ =>
    (match env.find? parent with | some (.thmInfo _) => true | _ => false) || hasTheoremParent env parent

private def body? : Lean.ConstantInfo → Option Lean.Expr
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

-- Lean 4.20 numbers hygienic names (binders, universe parameters, the helpers that deriving
-- adds) and abstracted proofs across the whole module, so each type and value is recorded
-- without those numbers: adding a declaration above it must not change it.
private def unhygienic (n : Lean.Name) : Lean.Name :=
  if n.hasMacroScopes then .anonymous else n

-- A name keeps its macro scopes in a prefix when Lean adds a suffix to a hygienic name, as in a helper's match_1.
private def erased (n : Lean.Name) : Lean.Name :=
  if n.hasMacroScopes then n.eraseMacroScopes else match n with
  | .str p s => .str (erased p) s
  | .num p i => .num (erased p) i
  | n => n

private def levelFree : Lean.Level → Lean.Level
  | .succ l => .succ (levelFree l)
  | .max a b => .max (levelFree a) (levelFree b)
  | .imax a b => .imax (levelFree a) (levelFree b)
  | .param n => .param n.eraseMacroScopes
  | l => l

-- Lean shares one match helper among the matches of the same shape in a module, so a declaration added
-- above can change which helper a match uses, and the splitter that the split tactic uses with it. A record
-- names every helper alike, and each declaration Lean derives from a helper by its suffix, and carries
-- their content.
private def shown (env : Lean.Environment) (n : Lean.Name) : Lean.Name :=
  if Lean.Meta.isMatcherCore env n then `_match else match n with
  | .str p s => if Lean.Meta.isMatcherCore env ((Lean.privateToUserName? p).getD p) then .str `_match s else erased n
  | _ => erased n

private def abstractedProof : Lean.Name → Bool
  | .str _ s => s.startsWith "_proof_" && s.length > 7 && (s.drop 7).all Char.isDigit
  | _ => false

-- A shared match helper takes its binder names from whichever match Lean made it for, and Lean 4.20 passes
-- them on to the alternatives of a match that uses it, so neither records binder names.
private partial def nameless : Lean.Expr → Lean.Expr
  | .lam _ t b i => .lam .anonymous (nameless t) (nameless b) i
  | .forallE _ t b i => .forallE .anonymous (nameless t) (nameless b) i
  | .letE _ t v b d => .letE .anonymous (nameless t) (nameless v) (nameless b) d
  | .app f a => .app (nameless f) (nameless a)
  | .mdata m e => .mdata m (nameless e)
  | .proj s i e => .proj s i (nameless e)
  | e => e

private partial def positionFree (env : Lean.Environment) : Lean.Expr → Lean.Expr
  | .lam n t b i => .lam (unhygienic n) (positionFree env t) (positionFree env b) i
  | .forallE n t b i => .forallE (unhygienic n) (positionFree env t) (positionFree env b) i
  | .letE n t v b d => .letE (unhygienic n) (positionFree env t) (positionFree env v) (positionFree env b) d
  | e@(.app f a) => match e.getAppFn with
    | head@(.const n _) =>
      if (shown env n).getRoot == `_match then
        Lean.mkAppN (positionFree env head) (e.getAppArgs.map (positionFree env ∘ nameless))
      else .app (positionFree env f) (positionFree env a)
    | _ => .app (positionFree env f) (positionFree env a)
  | .mdata m e => .mdata m (positionFree env e)
  | .proj s i e => .proj s i (positionFree env e)
  | .sort l => .sort (levelFree l)
  | .const n ls => if abstractedProof (erased n) then .const `_proof [] else .const (shown env n) (ls.map levelFree)
  | e => e

-- A recursive body can sit in an auxiliary: _f for structural recursion, _unary or _mutual
-- for well-founded recursion, and _unsafe_rec for the code that runs, the only body a partial def has.
-- Lean appends the suffix after a hygienic name's macro scopes, where ++ would put it before them.
private def auxBodies (env : Lean.Environment) (name : Lean.Name) : List (String × Lean.Expr) :=
  ["_f", "_unary", "_mutual", "_unsafe_rec"].filterMap fun aux => ((env.find? (.str name aux)).bind body?).map (aux, ·)

-- A hygienic constant or a match helper has no record of its own, so a record that refers to one carries its
-- type and value, and those of the hygienic constants and helpers they refer to in turn, each once.
-- Proofs stay out, as in every record.
open Lean in
private def followed (env : Environment) (roots : List Expr) : String := Id.run do
  let unrecorded (e : Expr) := e.getUsedConstants.filter fun c => shown env c != c && !abstractedProof (erased c)
  let mut queue := roots.foldl (fun acc e => acc ++ unrecorded e) #[]
  let mut seen : Array Name := #[]
  let mut out := ""
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    if seen.contains n then continue
    seen := seen.push n
    let some info := env.find? n | continue
    let parts := info.type :: (body? info).toList ++ (auxBodies env n).map (·.2)
    let shape := if (shown env n).getRoot == `_match then nameless else id
    out := out ++ s!"\n{shown env n}: {reprStr (parts.map (positionFree env ∘ shape))}"
    for e in parts do
      queue := queue ++ unrecorded e
  return out

-- The match helpers an expression uses, one per use, in the order they occur.
private partial def helperUses (env : Lean.Environment) : Lean.Expr → Array Lean.Name
  | .const n _ => if (shown env n).getRoot == `_match then #[n] else #[]
  | .app f a => helperUses env f ++ helperUses env a
  | .lam _ t b _ | .forallE _ t b _ => helperUses env t ++ helperUses env b
  | .letE _ t v b _ => helperUses env t ++ helperUses env v ++ helperUses env b
  | .mdata _ e | .proj _ _ e => helperUses env e
  | _ => #[]

-- A statement's identity when the mutation runner compares an original theorem, example or #guard with its
-- mutated copy: the frozen record's form of its type, without binder names, which change no statement.
-- That form names every match helper alike, so the content of the helper at each use is added: two
-- statements that use the same helpers at different places then differ, while a helper renamed differs not.
private def statementKey (env : Lean.Environment) (levels : List Lean.Name) (type : Lean.Expr) : String :=
  reprStr (levels.map (·.eraseMacroScopes), nameless (positionFree env type)) ++ followed env [type] ++
    reprStr ((helperUses env type).toList.map fun n => followed env [.const n []])

private def oneLine (s : String) : String :=
  (s.foldl (fun (acc, gap) c =>
    if c.isWhitespace then (acc, true) else ((if gap then acc.push ' ' else acc).push c, false)) ("", false)).1

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
private def audit (freezing : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let modules := (env.imports.map (·.module)).erase `Lean
  for module in env.header.moduleNames do IO.println s!"IMPORTED {module.toString (escape := false)}"
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
    -- Lean generates a reserved name, such as an equation lemma, only when a proof uses it.
    if isReservedName env name then continue
    -- Its check misses the equations of a private definition's matcher.
    if let .str parent _ := name then
      if Meta.isMatcherCore env parent && (← findDeclarationRanges? name).isNone then continue
    if Meta.isMatcherCore env name then continue
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
    let value := match body? info with
      | some v =>
        let auxes := auxBodies env name
        let bodies := auxes.foldl (init := reprStr (positionFree env v)) fun acc (aux, auxBody) =>
          acc ++ s!"\n{aux}: {reprStr (positionFree env auxBody)}"
        toJson (bodies ++ followed env (v :: auxes.map (·.2)))
      | none => Json.null
    let pp ← liftTermElabM <| Meta.ppExpr info.type
    let record := Json.mkObj [
      ("module", toJson env.header.moduleNames[idx.toNat]!.toString),
      ("name", toJson userName.toString), ("kind", toJson kind),
      ("typeExpr", toJson (reprStr (info.levelParams.map (·.eraseMacroScopes), positionFree env info.type) ++ followed env [info.type])),
      ("valueExpr", value), ("type", toJson pp.pretty)]
    IO.println s!"STATEMENT {record.compress}"
    if info matches .thmInfo _ then theorems := theorems.push (name, userName, idx)
  for (name, userName, idx) in theorems.qsort (·.1.toString < ·.1.toString) do
    let pairedWitness := match userName with
      | .str parent "witness" => theorems.any fun (_, user, owner) => owner == idx && user == parent
      | _ => false
    if name != userName || pairedWitness then continue
    if env.isProjectionFn name || Meta.isInstanceCore env name then continue
    if (← findDeclarationRanges? name).isNone then continue
    let witness? := theorems.find? fun (_, user, owner) => owner == idx && user == userName ++ `witness
    let line ← liftTermElabM <| tryCatchRuntimeEx
      (witnessLine (env.find? name).get! (witness?.bind (env.find? ·.1)))
      fun error => return s!"WITNESS unavailable {name}: {oneLine (← error.toMessageData.toString)}"
    IO.println line
  IO.println s!"AUDITED {audited} declarations"

open Lean Elab Command

private def point (p : Position) : Json := toJson (p.line, p.column)

-- An example's statement is the type of the local Lean binds for its header, and
-- a guard's is its term. Closing over the local context removes the ids of
-- section variables, which shift when an earlier command changes.
private def statement (trees : PersistentArray InfoTree) (check : Syntax) : IO Json := do
  let isExample := check.isOfKind ``Parser.Command.example
  let target := if isExample then check else check[1]
  let wanted (ti : TermInfo) := ti.stx.getPos? == target.getPos? &&
    (if isExample then ti.stx.isOfKind ``Parser.Command.declId && ti.expr.isFVar
     else ti.stx.getTailPos? == target.getTailPos?)
  let found := trees.foldl (init := none) fun found tree => found <|> tree.foldInfo (init := none)
    fun ctx info found => found <|> match info with
      | .ofTermInfo ti => if wanted ti then some (ctx, ti) else none
      | _ => none
  let some (ctx, ti) := found | return Json.null
  ctx.runMetaM ti.lctx do
    let e ← instantiateMVars (← if isExample then Meta.inferType ti.expr else pure ti.expr)
    let xs := ti.lctx.foldl (init := #[]) fun xs decl =>
      if decl.isImplementationDetail then xs else xs.push decl.toExpr
    let e ← Meta.mkLambdaFVars xs e
    let env ← getEnv
    return if e.hasFVar || e.hasMVar then Json.null else toJson (statementKey env [] e)

private def declarations (instances : Array (Nat × Nat)) : CommandElabM (Array Json) := do
  let env ← getEnv
  let fileMap ← getFileMap
  let names := env.constants.fold (fun acc name _ =>
    if env.isImportedConst name then acc else acc.push name) #[]
  let mut result := #[]
  for name in names do
    let some ranges ← findDeclarationRanges? name | continue
    let pos := (fileMap.ofPosition ranges.selectionRange.pos).byteIdx
    -- Local and scoped instances may no longer be registered in the final environment.
    let instanceDecl := Meta.isInstanceCore env name || instances.any fun (start, tail) =>
      start ≤ pos && pos < tail
    let info := (env.find? name).get!
    result := result.push <| Json.mkObj [
      ("name", toJson ((privateToUserName? name).getD name).toString),
      ("private", toJson (privateToUserName? name).isSome),
      ("theorem", toJson ((info matches .thmInfo _) && !env.isProjectionFn name && !instanceDecl)),
      ("type", toJson (statementKey env info.levelParams info.type)),
      ("start", point ranges.range.pos), ("end", point ranges.range.endPos)]
  return result


-- Print the errors in a message log to stderr, and say whether there were any.
private def printErrors (log : Lean.MessageLog) : IO Bool := do
  let errors := log.toList.filter (·.severity == .error)
  for msg in errors do
    IO.eprint (← msg.toString)
  return !errors.isEmpty

open Lean Elab in
unsafe def runAudit (freezing : Bool) (moduleList : String) : IO UInt32 := do
  let modules ← IO.FS.lines moduleList
  -- Types print as they would in a file that opens these namespaces, which the frozen records keep.
  let text := String.join ((#["Lean"] ++ modules).toList.map (s!"import {·}\n")) ++ "open Lean Elab Command\n"
  let inputCtx := Parser.mkInputContext text "<audit>"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  -- An import that fails, such as two modules that declare one name, stops the audit with Lean's error.
  if ← printErrors messages then return 1
  let state ← IO.processCommands inputCtx parserState (Command.mkState env messages {})
  if ← printErrors state.commandState.messages then return 1
  let (_, state) ← (Frontend.runCommandElabM (audit freezing)).run { inputCtx } |>.run state
  return if ← printErrors state.commandState.messages then 1 else 0

open Lean Elab Command in
unsafe def analyze (path : String) : IO UInt32 := do
  let inputCtx := Parser.mkInputContext (← IO.FS.readFile path) path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let state ← IO.processCommands inputCtx parserState (Command.mkState env messages {})
  let mut commands := #[]
  let mut instances := #[]
  for stx in state.commands do
    if let some instanceStx := stx.find? (·.isOfKind ``Parser.Command.instance) then
      if let (some start, some tail) := (instanceStx.getPos?, instanceStx.getTailPos?) then
        instances := instances.push (start.byteIdx, tail.byteIdx)
    let some start := stx.getPos? | continue
    let some tail := stx.getTailPos? | continue
    let propertyStx := stx.find? fun cmd =>
      cmd.isOfKind ``Parser.Command.guardCmd || cmd.isOfKind ``Parser.Command.example
    let property := match propertyStx with
      | some cmd => if cmd.isOfKind ``Parser.Command.guardCmd then "#guard" else "example"
      | none => ""
    let propertyStart := (propertyStx.bind Syntax.getPos?).getD start
    let propertyEnd := (propertyStx.bind Syntax.getTailPos?).getD tail
    commands := commands.push <| Json.mkObj [
      ("property", toJson property),
      ("statement", toJson (← propertyStx.mapM (statement state.commandState.infoState.trees))),
      ("start", point (inputCtx.fileMap.toPosition propertyStart)),
      ("end", point (inputCtx.fileMap.toPosition propertyEnd))]
  let (decls, _) ← (Frontend.runCommandElabM (declarations instances)).run { inputCtx } |>.run state
  let mut errors := #[]
  for msg in state.commandState.messages.toList do
    if msg.severity == .error then errors := errors.push (← msg.toJson)
  IO.println <| "AFV_LEAN " ++ (Json.mkObj [
    ("declarations", toJson decls), ("commands", toJson commands),
    ("errors", toJson errors)]).compress
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | ["audit", moduleList] => runAudit false moduleList
  | ["audit", "--freeze", moduleList] => runAudit true moduleList
  | ["analyze", path] => analyze path
  | _ => throw <| IO.userError "usage: lean-analysis.lean audit [--freeze] <module-list> | analyze <source.lean>"
