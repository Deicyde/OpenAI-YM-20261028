import ConcreteSU2
import Lean
import Lean.DeclarationRange

/-! Compare all imported YM declarations with the type and proof dependencies
of the theorem names in the combined release manifest. The parent column supplies one
path back to an endpoint when several endpoints share a declaration. -/
set_option autoImplicit false

open Lean in
private def auditModule (m : Name) : Bool :=
  Name.isPrefixOf `YM m || [`PublicTheory, `PublicWilson, `ChallengeSpec, `PublicView,
    `WilsonBridge, `HierarchyBridge, `TraceBridge, `ContactSpec, `ContactBridge,
    `Construction, `Solution, `ConcreteSU2].contains m

open Lean Elab Command in
run_cmd do
  let manifest ← IO.FS.readFile "verification/joint-headlines.txt"
  let roots := (manifest.splitOn "\n").map (fun s => s.trimAscii.toString) |>.filter (· != "") |>.map String.toName
  if roots.isEmpty || roots.eraseDups.length != roots.length then throwError "Empty or duplicate headline"
  let env := (← getEnv).setExporting false
  let mut used : Std.HashMap Name (Name × Name) := {}
  let mut seen : NameSet := {}
  let mut todo := roots.toArray.map fun n => (n, n, Name.anonymous)
  for r in roots do
    let some (.thmInfo _) := env.checked.get.find? r | throwError "Unknown headline theorem {r}"
  while !todo.isEmpty do
    let (n, root, parent) := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.checked.get.find? n | throwError "Missing declaration {n}"
    let some idx := env.getModuleIdxFor? n | throwError "Missing owner of {n}"
    unless auditModule env.header.modules[idx.toNat]!.module do continue
    used := used.insert n (root, parent)
    let mut refs := ci.getUsedConstantsAsSet
    if let .inductInfo i := ci then
      for other in i.all do refs := refs.insert other
    for child in refs do todo := todo.push (child, root, n)
  let mut totals : Std.HashMap Name (Nat × Nat) := {}
  let mut rows : Array (String × Name × Name) := #[]
  for m in env.header.modules do
    if auditModule m.module then totals := totals.insert m.module (0, 0)
  for (n, _) in env.checked.get.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.modules[idx.toNat]!.module
    unless totals.contains m do continue
    let (all, reach) := totals[m]!
    totals := totals.insert m (all + 1, reach + (if used.contains n then 1 else 0))
    rows := rows.push (s!"{m}\t{n}", m, n)
  let out ← IO.FS.Handle.mk "verification/declaration-usage.tsv" .write
  out.putStrLn "module\tdeclaration\tstatus\theadline_witness\timmediate_user\tsource_line"
  for (key, _, n) in rows.qsort (fun a b => a.1 < b.1) do
    let line := (← findDeclarationRangesCore? n).map (fun r => toString r.selectionRange.pos.line) |>.getD ""
    if roots.contains n then
      out.putStrLn s!"{key}\theadline\t{n}\t\t{line}"
    else if let some (root, parent) := used[n]? then
      out.putStrLn s!"{key}\tused\t{root}\t{parent}\t{line}"
    else out.putStrLn s!"{key}\toutside\t\t\t{line}"
  let mods ← IO.FS.Handle.mk "verification/module-usage.tsv" .write
  mods.putStrLn "module\tdeclarations\tused\toutside"
  let mut noOwner : Nat := 0
  for (m, (all, reach)) in totals.toArray.qsort (fun a b => toString a.1 < toString b.1) do
    if reach == 0 then noOwner := noOwner + 1
    mods.putStrLn s!"{m}\t{all}\t{reach}\t{all-reach}"
  logInfo m!"USAGE_PASS headlines={roots.length} project={rows.size} used={used.size} outside={rows.size-used.size} modules={totals.size} modulesWithNoUsedDeclaration={noOwner}"
