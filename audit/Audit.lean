/-
Audit for the RH Lean project. Run it only after `lake build` has succeeded, from the `lean/` directory:

    RH_AUDIT_OUT=/path/to/outdir lake env lean ../audit/Audit.lean

Stages run from quickest to slowest, and each writes its files as soon as it finishes, so the
process can be stopped at any point without losing earlier results. Progress, with timestamps:

    tail -f $RH_AUDIT_OUT/progress.log

Outputs in $RH_AUDIT_OUT (default ./audit-out):
  1 axioms.json        axioms behind each main theorem and each crux lemma (Lean's `collectAxioms`, the
                       function behind `#print axioms`). In Lean 4.33 this reads per-module records
                       written at build time; `leanchecker` is the independent re-check.
  2 crux.json          where each crux name resolves
    statements.txt     the crux definitions and lemmas, fully pretty-printed (fully qualified names)
  3 deps.json          how much of the project `riemannHypothesis` uses, by library, and every axiom
                       reached by walking its proof terms (independent of the build-time records)
    module-usage.tsv   for every project module, how many of its declarations that proof uses
    crux.json          rewritten with, for each match, whether `riemannHypothesis` depends on it
  4 crux-weight.json   size of each crux lemma's own dependency closure, within a time budget

The dependency walks (stages 3 and 4) run in parallel on all cores (`LEAN_NUM_THREADS`).
Environment knobs: RH_AUDIT_MAX_MATCHES (statements printed per crux name, default 8),
RH_AUDIT_PP_LIMIT (terms with more distinct subterms than this are not printed, default 100000),
RH_AUDIT_WEIGHT_MINUTES (time budget for stage 4, default 60; 0 skips it).
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

/-- Constants a declaration refers to directly: through its type, its value, and for inductive
types, constructors and recursors, the declarations they belong with. -/
def refsOf (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let refs := ci.type.getUsedConstants
    let refs := match ci.value? (allowOpaque := true) with
      | some v => refs ++ v.getUsedConstants
      | none => refs
    match ci with
    | .inductInfo i => refs ++ i.ctors.toArray
    | .ctorInfo c => refs.push c.induct
    | .recInfo r => refs ++ r.all.toArray
    | _ => refs

/-- Every constant reachable from `roots`. Breadth-first. Each level's declarations are dealt out
round-robin into many small batches that run as parallel tasks (walking proof terms is nearly all
of the cost, and neighbouring declarations tend to be heavy together). Every minute it reports
progress and names any declaration that has been walked for more than two minutes. -/
def closure (env : Environment) (roots : Array Name) (say : String → IO Unit) :
    IO (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut frontier : Array Name := #[]
  for r in roots do
    unless seen.contains r do
      seen := seen.insert r
      frontier := frontier.push r
  let mut level := 0
  let mut lastSay ← IO.monoMsNow
  while !frontier.isEmpty do
    level := level + 1
    let k := max 1 (min 8192 ((frontier.size + 3) / 4))
    let mut batches : Array (Array Name) := Array.replicate k #[]
    for i in [0:frontier.size] do
      batches := batches.modify (i % k) (·.push frontier[i]!)
    let mut tasks : Array (Task (Except IO.Error (Array (Array Name)))) := #[]
    let mut current : Array (IO.Ref (Name × Nat)) := #[]
    for b in batches do
      let cur ← IO.mkRef (Name.anonymous, 0)
      let t ← IO.asTask do
        let mut out : Array (Array Name) := #[]
        for n in b do
          cur.set (n, ← IO.monoMsNow)
          out := out.push (refsOf env n)
        cur.set (Name.anonymous, 0)
        return out
      tasks := tasks.push t
      current := current.push cur
    let mut next : Array Name := #[]
    for j in [0:tasks.size] do
      let t := tasks[j]!
      while !(← IO.hasFinished t) do
        IO.sleep 20
        let now ← IO.monoMsNow
        if now - lastSay ≥ 60000 then
          let mut slow : Array String := #[]
          for c in current do
            let (n, st) ← c.get
            if st > 0 && now - st ≥ 120000 then
              slow := slow.push s!"{n} ({(now - st) / 60000} min)"
          say s!"  walking: level {level}, batch {j}/{tasks.size} of {frontier.size} declarations, {seen.size} constants found so far{if slow.isEmpty then "" else s!"; slow: {slow.toList.take 6}"}"
          lastSay := now
      match t.get with
      | .ok arrs =>
        for refs in arrs do
          for r in refs do
            unless seen.contains r do
              seen := seen.insert r
              next := next.push r
      | .error e => say s!"  error while walking: {e}"
    frontier := next
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

/-- Pretty-print `e` unless it has more than `limit` distinct subterms (printing is slow on huge terms). -/
def ppCapped (limit : Nat) (label : String) (e : Expr) : CommandElabM String := do
  let k ← e.numObjs
  if k > limit then
    return s!"{label}: not printed ({k} distinct subterms; raise RH_AUDIT_PP_LIMIT to print it)\n"
  let f ← liftTermElabM <| ppExpr e
  return s!"{label}:\n{f.pretty 120}\n"

def ppConst (n : Name) : CommandElabM String := do
  let env ← getEnv
  let limit ← envNat "RH_AUDIT_PP_LIMIT" 100000
  let some ci := env.find? n | return s!"## {n}\nNOT FOUND\n\n"
  let mut out := s!"## {n}\nkind: {kindOf ci}   module: {moduleOf env n}\n"
  try
    out := out ++ (← ppCapped limit "type" ci.type)
    match ci with
    | .defnInfo d =>
      out := out ++ (← ppCapped limit "value" d.value)
    | .inductInfo i =>
      for c in i.ctors do
        if let some cc := env.find? c then
          out := out ++ (← ppCapped limit s!"constructor {c}" cc.type)
    | _ => pure ()
  catch e =>
    out := out ++ s!"ERROR while printing: {← e.toMessageData.toString}\n"
  return out ++ "\n"

/-- One crux name and its matches; `used?` is the headline closure once it is known. -/
def cruxRow (env : Environment) (used? : Option (Std.HashSet Name)) (role suf : String)
    (ns : Array Name) : Json :=
  let usedField (n : Name) : List (String × Json) :=
    match used? with
    | some s => [("usedByMain", toJson (s.contains n))]
    | none => []
  Json.mkObj <|
    [("suffix", toJson suf), ("role", toJson role), ("matches", toJson ns.size)] ++
    (match used? with
     | some s => [("usedByMain", toJson (ns.filter s.contains).size)]
     | none => []) ++
    [("constants", Json.arr <| ns.map fun n => Json.mkObj <|
      [("name", toJson (toString n)), ("module", toJson (toString (moduleOf env n))),
       ("kind", toJson ((env.find? n).map kindOf |>.getD "?"))] ++ usedField n)]

def run (mainThms : Array Name) (cruxThms cruxDefs : Array String) : CommandElabM Unit := do
  let dir ← outDir
  let l : Log := { dir, t0 := ← IO.monoMsNow }
  let env ← getEnv
  l.say s!"environment loaded: {env.header.moduleNames.size} modules, {env.constants.map₁.size} imported constants"
  let some root := mainThms[0]? | l.say "no main theorem configured"; return

  -- Crux names (one pass over all constants).
  let hits := resolveSuffixes env (cruxThms ++ cruxDefs)
  let unresolved := hits.filter (·.2.isEmpty) |>.map (·.1)
  let thmHits := hits.extract 0 cruxThms.size
  let defHits := hits.extract cruxThms.size hits.size
  l.say s!"located crux names; unresolved: {unresolved}"

  -- 1. Axioms (fast: build-time records).
  l.say "stage 1/4: axioms of the main theorems and every crux lemma match"
  let mut axRows : Array Json := #[]
  for n in mainThms ++ thmHits.foldl (init := #[]) (fun acc (_, ns) => acc ++ ns) do
    axRows := axRows.push (← axiomsRow n)
  IO.FS.writeFile (dir / "axioms.json") (Json.arr axRows).pretty
  l.say s!"wrote axioms.json; {root}: {axRows[0]!.compress}"

  -- 2. Crux locations and statements.
  let writeCrux (used? : Option (Std.HashSet Name)) : IO Unit :=
    IO.FS.writeFile (dir / "crux.json") <| (Json.mkObj
      [("root", toJson (toString root)), ("unresolved", toJson unresolved),
       ("lemmas", Json.arr <| thmHits.map fun (suf, ns) => cruxRow env used? "lemma" suf ns),
       ("definitions", Json.arr <| defHits.map fun (suf, ns) => cruxRow env used? "definition" suf ns)]).pretty
  writeCrux none
  let maxPer ← envNat "RH_AUDIT_MAX_MATCHES" 8
  l.say s!"stage 2/4: wrote crux.json; pretty-printing statements (up to {maxPer} matches per crux name)"
  IO.FS.writeFile (dir / "statements.txt") ""
  let h ← IO.FS.Handle.mk (dir / "statements.txt") .append
  for n in mainThms do
    h.putStr (← ppConst n)
  let total := (defHits ++ thmHits).foldl (init := 0) fun acc (_, ns) => acc + min ns.size maxPer
  let mut k := 0
  for (suf, ns) in defHits ++ thmHits do
    h.putStr s!"################ {suf}  ({ns.size} match(es); showing up to {maxPer})\n\n"
    for n in ns.extract 0 maxPer do
      k := k + 1
      l.say s!"  printing {k}/{total}: {n}"
      let t ← IO.monoMsNow
      h.putStr (← ppConst n)
      h.flush
      let dt := (← IO.monoMsNow) - t
      if dt > 30000 then l.say s!"  (that took {dt / 1000}s)"
  h.flush
  l.say "wrote statements.txt"

  -- 3. Dependency closure of the headline theorem.
  l.say s!"stage 3/4: walking every proof term {root} depends on"
  let s ← closure env #[root] l.say
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
  writeCrux (some s)
  l.say s!"wrote deps.json, module-usage.tsv, crux.json: {s.size} constants in the closure; axioms reached: {axInClosure}"

  -- 4. Dependency weight of each crux lemma (one match per name, preferring ones the headline
  --    proof uses), within a time budget.
  let budget := (← envNat "RH_AUDIT_WEIGHT_MINUTES" 60) * 60000
  let tStart ← IO.monoMsNow
  let mut weights : Array Json := #[]
  for (_, ns) in thmHits do
    let some n := (ns.filter s.contains ++ ns)[0]? | continue
    if (← IO.monoMsNow) - tStart ≥ budget then
      l.say "stage 4/4: time budget used up, stopping"
      break
    l.say s!"stage 4/4: weight of {n}"
    let w ← closure env #[n] l.say
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
