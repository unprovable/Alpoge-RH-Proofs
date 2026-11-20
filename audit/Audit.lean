/-
Audit for the RH Lean project. Run it only after `lake build` has succeeded, from the `lean/` directory:

    RH_AUDIT_OUT=/path/to/outdir lake env lean ../audit/Audit.lean

It writes into $RH_AUDIT_OUT (default ./audit-out):
  axioms.json          axioms behind each main theorem and each crux lemma, with non-standard ones flagged
  deps.json            how much of the project the proof of `riemannHypothesis` actually uses, by library
  module-usage.tsv     for every project module, how many of its declarations that proof uses
  crux-weight.json     the same dependency count for each crux lemma on its own
  statements.txt       the crux definitions and lemmas, fully pretty-printed (fully qualified names)
-/
import Main
import Lean

open Lean Elab Command Meta

namespace RHAudit

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Top-level directories of the project's own source tree. -/
def projectRoots : List String :=
  ["BuildAid", "CompanionTheory", "Development", "Formalism", "GroundTheory", "Lemmata",
   "PositivityTheory", "ReciprocityTheory", "Supplements", "Statements", "Main"]

def rootOf (m : Name) : String :=
  match m.components.head? with
  | some r => r.toString
  | none => "?"

def isProjectModule (m : Name) : Bool := projectRoots.contains (rootOf m)

def outDir : IO System.FilePath := do
  let d : System.FilePath := (← IO.getEnv "RH_AUDIT_OUT").getD "audit-out"
  IO.FS.createDirAll d
  return d

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `_this_file

/-- `nameEndsWith n suf`: the components of `suf` are a trailing segment of `n`'s. -/
def nameEndsWith : Name → Name → Bool
  | _, .anonymous => true
  | .str p s, .str q t => s == t && nameEndsWith p q
  | .num p a, .num q b => a == b && nameEndsWith p q
  | _, _ => false

/-- Every constant reachable from `roots` through types, values, constructors and recursors. -/
def closure (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut refs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      refs := refs ++ v.getUsedConstants
    match ci with
    | .inductInfo i => refs := refs ++ i.ctors.toArray
    | .ctorInfo c => refs := refs.push c.induct
    | .recInfo r => refs := refs ++ r.all.toArray
    | _ => pure ()
    for r in refs do
      unless seen.contains r do stack := stack.push r
  return seen

/-- Resolve dotted suffixes such as "Top.VWin" to every matching non-internal constant. -/
def resolveSuffixes (env : Environment) (sufs : Array String) : Array (String × Array Name) := Id.run do
  let parsed := sufs.map fun s => (s, s.toName)
  let lasts : Std.HashSet String := parsed.foldl (init := {}) fun acc (_, n) =>
    match n with
    | .str _ t => acc.insert t
    | _ => acc
  let mut hits : Std.HashMap String (Array Name) := {}
  for (n, _) in env.constants.toList do
    match n with
    | .str _ t =>
      if lasts.contains t && !n.isInternalDetail then
        for (s, suf) in parsed do
          if nameEndsWith n suf then
            hits := hits.insert s ((hits.getD s #[]).push n)
    | _ => pure ()
  return parsed.map fun (s, _) => (s, (hits.getD s #[]).qsort Name.lt)

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def axiomsJson (names : Array Name) : CommandElabM Json := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for n in names do
    if !env.contains n then
      rows := rows.push (Json.mkObj [("name", toString n), ("found", false)])
      continue
    let axs ← collectAxioms n
    let nonstd := axs.filter (fun a => !standardAxioms.contains a)
    rows := rows.push <| Json.mkObj
      [("name", toString n), ("found", true), ("module", toString (moduleOf env n)),
       ("axioms", toJson (axs.map toString)), ("nonStandardAxioms", toJson (nonstd.map toString))]
  return Json.arr rows

def countByModule (env : Environment) (s : Std.HashSet Name) : Std.HashMap Name Nat :=
  s.fold (init := {}) fun acc n => let m := moduleOf env n; acc.insert m (acc.getD m 0 + 1)

def depsSummary (env : Environment) (byMod : Std.HashMap Name Nat) (total : Nat) : Json := Id.run do
  let projMods := env.header.moduleNames.filter isProjectModule
  let mut perRoot : Std.HashMap String (Nat × Nat × Nat) := {}  -- (modules, modules used, constants used)
  for m in projMods do
    let r := rootOf m
    let (a, b, c) := perRoot.getD r (0, 0, 0)
    let k := byMod.getD m 0
    perRoot := perRoot.insert r (a + 1, b + (if k > 0 then 1 else 0), c + k)
  let mut nonProject : Std.HashMap String Nat := {}
  for (m, k) in byMod.toList do
    unless isProjectModule m do
      nonProject := nonProject.insert (rootOf m) (nonProject.getD (rootOf m) 0 + k)
  let roots := perRoot.toList.map fun (r, (a, b, c)) =>
    (r, Json.mkObj [("modules", toJson a), ("modulesUsed", toJson b), ("constantsUsed", toJson c)])
  let usedMods := projMods.filter (fun m => byMod.getD m 0 > 0)
  return Json.mkObj
    [("constantsInClosure", toJson total),
     ("projectModules", toJson projMods.size),
     ("projectModulesUsed", toJson usedMods.size),
     ("byProjectLibrary", Json.mkObj roots),
     ("constantsFromOutsideProject", Json.mkObj (nonProject.toList.map fun (r, k) => (r, toJson k)))]

def ppConst (n : Name) : CommandElabM String := do
  let env ← getEnv
  let some ci := env.find? n | return s!"## {n}\nNOT FOUND\n"
  let mut out := s!"## {n}\nkind: {kindOf ci}   module: {moduleOf env n}\n"
  let ty ← liftTermElabM <| ppExpr ci.type
  out := out ++ s!"type:\n{ty.pretty 120}\n"
  match ci with
  | .defnInfo d =>
    let v ← liftTermElabM <| ppExpr d.value
    out := out ++ s!"value:\n{v.pretty 120}\n"
  | .inductInfo i =>
    for c in i.ctors do
      if let some cc := env.find? c then
        let ct ← liftTermElabM <| ppExpr cc.type
        out := out ++ s!"constructor {c}:\n{ct.pretty 120}\n"
  | _ => pure ()
  return out ++ "\n"

def run (mainThms : Array Name) (cruxThms cruxDefs : Array String) : CommandElabM Unit := do
  let dir ← outDir
  let env ← getEnv
  let report (msg : String) : CommandElabM Unit := do
    logInfo msg
    (← IO.getStdout).putStrLn s!"[audit] {msg}"
  -- Resolve the crux names (suffix match, so namespaces need not be exact).
  let thmHits := resolveSuffixes env cruxThms
  let defHits := resolveSuffixes env cruxDefs
  let unresolved := (thmHits ++ defHits).filter (·.2.isEmpty) |>.map (·.1)
  report s!"unresolved suffixes: {unresolved}"
  let cruxThmNames := thmHits.foldl (init := #[]) fun acc (_, ns) => acc ++ ns
  -- 1. Axioms.
  let ax ← axiomsJson (mainThms ++ cruxThmNames)
  IO.FS.writeFile (dir / "axioms.json") ax.pretty
  report "wrote axioms.json"
  -- 2. Dependency closure of the main theorem.
  if let some root := mainThms[0]? then
    let s := closure env #[root]
    let byMod := countByModule env s
    IO.FS.writeFile (dir / "deps.json") (depsSummary env byMod s.size).pretty
    let mut tsv := "module\tconstants_used\n"
    for m in env.header.moduleNames do
      if isProjectModule m then tsv := tsv ++ s!"{m}\t{byMod.getD m 0}\n"
    IO.FS.writeFile (dir / "module-usage.tsv") tsv
    report s!"wrote deps.json, module-usage.tsv ({s.size} constants in closure of {root})"
  -- 3. Weight of each crux lemma: size of its own dependency closure inside the project.
  --    (At most 5 matches per suffix, to bound the run time.)
  let mut weights : Array Json := #[]
  for n in thmHits.foldl (init := #[]) (fun acc (_, ns) => acc ++ ns.extract 0 5) do
    let s := closure env #[n]
    let byMod := countByModule env s
    let projMods := byMod.toList.filter (fun (m, _) => isProjectModule m)
    let projConsts := projMods.foldl (init := 0) fun acc (_, k) => acc + k
    weights := weights.push <| Json.mkObj
      [("name", toString n), ("constantsInClosure", toJson s.size),
       ("projectConstants", toJson projConsts), ("projectModules", toJson projMods.length)]
  IO.FS.writeFile (dir / "crux-weight.json") (Json.arr weights).pretty
  report "wrote crux-weight.json"
  -- 4. Pretty-printed statements.
  let mut txt := ""
  for (s, ns) in defHits ++ thmHits do
    txt := txt ++ s!"################ {s}  ({ns.size} match(es))\n"
    for n in ns do txt := txt ++ (← ppConst n)
  for n in mainThms do txt := txt ++ (← ppConst n)
  IO.FS.writeFile (dir / "statements.txt") txt
  report "wrote statements.txt"

end RHAudit

set_option maxHeartbeats 0
set_option pp.fullNames true
set_option pp.proofs false
set_option pp.deepTerms true
set_option pp.maxSteps 5000000

-- CONFIG BEGIN
/-- The five headline theorems in `Main.lean`; the first is used for the dependency count. -/
def RHAudit.mainTheorems : Array Name :=
  #[`riemannHypothesis, `riemannZeta_eq_zero_re, `LFunction_ne_zero_of_half_lt_re,
    `LFunction_eq_zero_re, `LFunction_eq_zero_re_of_isPrimitive,
    `RiemannHypothesis, `RiemannZetaZerosOnLine, `DirichletLNonvanishingRightOfHalf,
    `DirichletLZerosOnLine, `PrimitiveDirichletLZerosOnLine]

/-- Crux lemmas identified by reading the source (dotted suffixes; every match is audited). -/
def RHAudit.cruxTheorems : Array String :=
  #["UpperTheory.FinalTheorems.everyCharacter", "UpperTheory.Top.zeroFreeAll_of_topG",
    "UpperTheory.Top.supplyChi", "UpperTheory.Top.shapeWin",
    "UpperTheory.Top.every_character_of_green_v_win",
    "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
    "UpperTheory.One.vwin_of_row", "UpperTheory.Zero.LLC.recTExists",
    "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter",
    "Formalism.HC.zeroFreeOn_of_tiedWin_cyc", "formB", "level_gm_le_on_family_scales",
    "core_gm", "ch_top", "ch_balance", "ch_core", "landau_window", "boundedTw",
    "hostOfField", "divinN_of_hypV", "link_gl", "galoisRepresentations_of_thetaLift"]

/-- Crux definitions whose full statements an expert should read. -/
def RHAudit.cruxDefinitions : Array String :=
  #["UpperTheory.EveryCharacter", "UpperTheory.Top.VWin", "UpperTheory.Top.VWinAt",
    "UpperTheory.Top.VVle", "UpperTheory.Top.VAt", "UpperTheory.Top.TopG",
    "Formalism.HC.Level.Gm", "Formalism.HC.EAtH", "FormBAt", "ChainTied", "SizeData₂",
    "ErrWindows", "RestSize", "LinkDIV_at", "LinkG_at", "LinkN_at", "LinkS", "HostGood",
    "ThinOK", "BoxH", "HostExW", "GChi", "HypV", "FamilyClassConnected",
    "UpperTheory.GalStar.Row0b", "UpperTheory.Zero.LLC.IsRecT",
    "Formalism.GaloisCohomology.shaLen", "Formalism.GaloisCohomology.LData"]
-- CONFIG END

run_cmd RHAudit.run RHAudit.mainTheorems RHAudit.cruxTheorems RHAudit.cruxDefinitions
