/-
Kernel re-check of a list of modules, one after another in a single process.

`replayFromImports` below is copied unchanged from Lean 4.33.1's `leanchecker`
(src/lean/LeanChecker.lean): load the module's imports, then replay every declaration of the
module through the kernel (`Lean.Environment.replay`). The only difference from running
`leanchecker <module>` is the driver: leanchecker scans every .olean on the search path at start-up
(about a minute on this project) and runs its targets as parallel tasks in one process, where only
the first task can map the compiled files into memory and the rest load them into RAM. Here each
module is checked in turn and its memory released before the next.

Usage: rhcheck <module>...   or   rhcheck --list <file with one module per line>
Prints, flushed, per module: "start <m>", then "ok <m> <seconds>" or "FAIL <m> <error>".
-/
import Lean
open Lean

unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  env'.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods ← match args with
    | ["--list", f] => pure ((← IO.FS.lines f).toList.filter (· ≠ ""))
    | _ => pure args
  let out ← IO.getStdout
  let mut failed := 0
  for m in mods do
    out.putStrLn s!"start\t{m}"
    out.flush
    let t ← IO.monoMsNow
    try
      replayFromImports m.toName
      let ds := ((← IO.monoMsNow) - t) / 100
      out.putStrLn s!"ok\t{m}\t{ds / 10}.{ds % 10}"
    catch e =>
      failed := failed + 1
      out.putStrLn s!"FAIL\t{m}\t{(toString e).replace "\n" " | "}"
    out.flush
  return if failed == 0 then 0 else 1
