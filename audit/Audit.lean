/-
Audit for the RH Lean project. Run it only after `lake build` has succeeded, from the `lean/` directory:

    RH_AUDIT_OUT=/path/to/outdir lake env lean ../audit/Audit.lean

On this project one pass over a top-level proof's dependencies is expensive, so the stages run
from most to least valuable. Each stage writes its file as soon as it finishes, so the process
can be stopped at any point without losing earlier results. Progress, with timestamps:

    tail -f $RH_AUDIT_OUT/progress.log

Outputs in $RH_AUDIT_OUT (default ./audit-out):
  1 axioms.json        axioms behind `riemannHypothesis` (Lean's `collectAxioms`, as `#print axioms`)
  2 deps.json          how much of the project that proof uses, by library, plus every axiom in it
    module-usage.tsv   for every project module, how many of its declarations that proof uses
  3 crux.json          where each crux name resolves, and whether `riemannHypothesis` depends on it
                       (an axiom check per crux lemma is unnecessary: whatever the main proof uses
                       inherits its axioms, which stage 1 already lists)
  4 statements.txt     the crux definitions and lemmas, fully pretty-printed (fully qualified names)
  5 axioms.json        extended with the other main theorems
  6 crux-weight.json   size of each crux lemma's own dependency closure, within a time budget

Environment knobs: RH_AUDIT_MAX_MATCHES (statements printed per crux name, default 8),
RH_AUDIT_WEIGHT_MINUTES (time budget for stage 6, default 60; 0 skips it).
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

def envNat (var : String) (dflt : Nat) : IO Nat :=
  return ((← IO.getEnv var).bind String.toNat?).getD dflt

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `_this_file

/-- Wall-clock time (UTC), for the progress log. -/
def clock : IO String := do
  try
    let o ← IO.Process.output { cmd := "date", args := #["-u", "+%H:%M:%S"] }
    return o.stdout.replace "\n" ""
  catch _ => return "--:--:--"

/-- Progress lines go to `progress.log` directly (flushed), because output printed during
elaboration is only shown once the whole command finishes. -/
structure Log where
  dir : System.FilePath
  t0 : Nat

def Log.say (l : Log) (msg : String) : IO Unit := do
  let s := ((← IO.monoMsNow) - l.t0) / 1000
  let line := s!"[audit] {← clock} (+{s / 3600}h{s % 3600 / 60}m{s % 60}s) {msg}"
  let h ← IO.FS.Handle.mk (l.dir / "progress.log") .append
  h.putStrLn line
  h.flush

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

def axiomsRow (n : Name) : CommandElabM Json := do
  let env ← getEnv
  unless env.contains n do
    return Json.mkObj [("name", toString n), ("found", false)]
  let axs ← collectAxioms n
  let nonstd := axs.filter (fun a => !standardAxioms.contains a)
  return Json.mkObj
    [("name", toString n), ("found", true), ("module", toString (moduleOf env n)),
     ("axioms", toJson (axs.map toString)), ("nonStandardAxioms", toJson (nonstd.map toString))]

def countByModule (env : Environment) (s : Std.HashSet Name) : Std.HashMap Name Nat :=
  s.fold (init := {}) fun acc n => let m := moduleOf env n; acc.insert m (acc.getD m 0 + 1)

def depsSummary (env : Environment) (byMod : Std.HashMap Name Nat) (total : Nat) :
    List (String × Json) := Id.run do
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
  return [("constantsInClosure", toJson total),
     ("projectModules", toJson projMods.size),
     ("projectModulesUsed", toJson usedMods.size),
     ("byProjectLibrary", Json.mkObj roots),
     ("constantsFromOutsideProject", Json.mkObj (nonProject.toList.map fun (r, k) => (r, toJson k)))]

def ppConst (n : Name) : CommandElabM String := do
  let env ← getEnv
  let some ci := env.find? n | return s!"## {n}\nNOT FOUND\n\n"
  let mut out := s!"## {n}\nkind: {kindOf ci}   module: {moduleOf env n}\n"
  try
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
  catch e =>
    out := out ++ s!"ERROR while printing: {← e.toMessageData.toString}\n"
  return out ++ "\n"

def run (mainThms : Array Name) (cruxThms cruxDefs : Array String) : CommandElabM Unit := do
  let dir ← outDir
  let l : Log := { dir, t0 := ← IO.monoMsNow }
  let env ← getEnv
  l.say s!"environment loaded: {env.header.moduleNames.size} modules, {env.constants.map₁.size} imported constants"
  let some root := mainThms[0]? | l.say "no main theorem configured"; return

  -- 1. Axioms of the headline theorem.
  l.say s!"stage 1/6: axioms of {root} (collectAxioms, the function behind #print axioms)"
  let mut axRows : Array Json := #[← axiomsRow root]
  IO.FS.writeFile (dir / "axioms.json") (Json.arr axRows).pretty
  l.say s!"wrote axioms.json: {axRows[0]!.compress}"

  -- 2. Dependency closure of the headline theorem.
  l.say s!"stage 2/6: dependency closure of {root}"
  let s := closure env #[root]
  let byMod := countByModule env s
  let axInClosure := (s.fold (init := #[]) fun acc n =>
    match env.find? n with
    | some (.axiomInfo _) => acc.push n
    | _ => acc).qsort Name.lt
  IO.FS.writeFile (dir / "deps.json") <| (Json.mkObj <|
    ("root", toJson (toString root)) :: ("axiomsInClosure", toJson (axInClosure.map toString)) ::
      depsSummary env byMod s.size).pretty
  let mut tsv := "module\tconstants_used\n"
  for m in env.header.moduleNames do
    if isProjectModule m then tsv := tsv ++ s!"{m}\t{byMod.getD m 0}\n"
  IO.FS.writeFile (dir / "module-usage.tsv") tsv
  l.say s!"wrote deps.json, module-usage.tsv: {s.size} constants in the closure; axioms among them: {axInClosure}"

  -- 3. Where the crux names resolve, and whether the headline proof uses them.
  l.say "stage 3/6: locating crux names"
  let hits := resolveSuffixes env (cruxThms ++ cruxDefs)
  let unresolved := hits.filter (·.2.isEmpty) |>.map (·.1)
  -- Matches the headline proof uses come first.
  let ordered := hits.map fun (suf, ns) => (suf, ns.filter s.contains ++ ns.filter (!s.contains ·))
  let thmHits := ordered.extract 0 cruxThms.size
  let defHits := ordered.extract cruxThms.size ordered.size
  let cruxRow (role : String) (suf : String) (ns : Array Name) : Json :=
    Json.mkObj [("suffix", toJson suf), ("role", toJson role), ("matches", toJson ns.size),
      ("usedByMain", toJson (ns.filter s.contains).size),
      ("constants", Json.arr <| ns.map fun n => Json.mkObj
        [("name", toJson (toString n)), ("module", toJson (toString (moduleOf env n))),
         ("kind", toJson ((env.find? n).map kindOf |>.getD "?")),
         ("usedByMain", toJson (s.contains n))])]
  IO.FS.writeFile (dir / "crux.json") <| (Json.mkObj
    [("root", toJson (toString root)), ("unresolved", toJson unresolved),
     ("lemmas", Json.arr <| thmHits.map fun (suf, ns) => cruxRow "lemma" suf ns),
     ("definitions", Json.arr <| defHits.map fun (suf, ns) => cruxRow "definition" suf ns)]).pretty
  l.say s!"wrote crux.json; unresolved: {unresolved}"

  -- 4. Pretty-printed statements, written as they are produced.
  let maxPer ← envNat "RH_AUDIT_MAX_MATCHES" 8
  l.say s!"stage 4/6: pretty-printing statements (up to {maxPer} matches per crux name)"
  IO.FS.writeFile (dir / "statements.txt") ""
  let h ← IO.FS.Handle.mk (dir / "statements.txt") .append
  for n in mainThms do
    h.putStr (← ppConst n)
  for (suf, ns) in defHits ++ thmHits do
    h.putStr s!"################ {suf}  ({ns.size} match(es), {(ns.filter s.contains).size} used by {root}; showing up to {maxPer})\n\n"
    for n in ns.extract 0 maxPer do
      let t ← IO.monoMsNow
      h.putStr (← ppConst n)
      h.flush
      let dt := (← IO.monoMsNow) - t
      if dt > 60000 then l.say s!"  printing {n} took {dt / 1000}s"
  h.flush
  l.say "wrote statements.txt"

  -- 5. Axioms of the other main theorems (only those outside the headline closure need a pass).
  for n in mainThms.extract 1 mainThms.size do
    if s.contains n then
      axRows := axRows.push <| Json.mkObj [("name", toString n), ("found", true),
        ("axioms", toJson "subset of the first row: it is in that theorem's dependency closure")]
    else
      l.say s!"stage 5/6: axioms of {n}"
      axRows := axRows.push (← axiomsRow n)
    IO.FS.writeFile (dir / "axioms.json") (Json.arr axRows).pretty
  l.say "wrote axioms.json for all main theorems"

  -- 6. Dependency weight of each crux lemma (one match per name), within a time budget.
  let budget := (← envNat "RH_AUDIT_WEIGHT_MINUTES" 60) * 60000
  let tStart ← IO.monoMsNow
  let mut weights : Array Json := #[]
  for (_, ns) in thmHits do
    let some n := ns[0]? | continue
    if (← IO.monoMsNow) - tStart ≥ budget then
      l.say "stage 6/6: time budget used up, stopping"
      break
    l.say s!"stage 6/6: weight of {n}"
    let w := closure env #[n]
    let wMod := countByModule env w
    let projMods := wMod.toList.filter (fun (m, _) => isProjectModule m)
    let projConsts := projMods.foldl (init := 0) fun acc (_, k) => acc + k
    weights := weights.push <| Json.mkObj
      [("name", toString n), ("usedByMain", toJson (s.contains n)), ("constantsInClosure", toJson w.size),
       ("projectConstants", toJson projConsts), ("projectModules", toJson projMods.length)]
    IO.FS.writeFile (dir / "crux-weight.json") (Json.arr weights).pretty
  l.say "finished"

end RHAudit

set_option maxHeartbeats 0
set_option pp.fullNames true
set_option pp.proofs false
set_option pp.deepTerms true
set_option pp.maxSteps 5000000

-- CONFIG BEGIN
/-- The headline theorems in `Main.lean` and the statements they prove; the first is the root of
the dependency count. -/
def RHAudit.mainTheorems : Array Name :=
  #[`riemannHypothesis, `riemannZeta_eq_zero_re, `LFunction_ne_zero_of_half_lt_re,
    `LFunction_eq_zero_re, `LFunction_eq_zero_re_of_isPrimitive,
    `RiemannHypothesis, `RiemannZetaZerosOnLine, `DirichletLNonvanishingRightOfHalf,
    `DirichletLZerosOnLine, `PrimitiveDirichletLZerosOnLine]

/-- Crux lemmas identified by reading the source (dotted suffixes; every match is located). -/
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
