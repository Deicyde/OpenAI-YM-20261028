import ConcreteSU2
import Lean
import Lean.Replay

/-! Recheck the project declarations reachable from the advertised theorem terms in a
kernel environment which initially contains only the pinned external libraries. -/
set_option autoImplicit false

namespace IndependentAudit
open Lean Elab Command

private def projectModule (m : Name) : Bool :=
  Name.isPrefixOf `YM m || [`PublicTheory, `PublicWilson, `ChallengeSpec, `ContactSpec,
    `PublicView, `WilsonBridge, `HierarchyBridge, `TraceBridge, `ContactBridge,
    `Construction, `Solution, `Challenge, `ConcreteSU2].contains m

private def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

def replayProofs (roots : Array Name) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let reference ← liftIO <| importModules #[{module := `Challenge}] {}
  for m in reference.header.modules do
    if projectModule m.module && !([`PublicTheory, `PublicWilson, `ChallengeSpec, `Challenge] : List Name).contains m.module then
      throwError "Implementation module in the reference statement: {m.module}"
  let endpoint := `YangMills.jointExistence
  let some (.thmInfo challenge) := reference.checked.get.find? endpoint | throwError "Missing challenge"
  let some (.thmInfo solution) := env.checked.get.find? endpoint | throwError "Missing solution"
  unless challenge.type == solution.type && challenge.levelParams == solution.levelParams do
    throwError "Challenge and solution theorem types differ"
  logInfo m!"TYPE_MATCH {endpoint}"
  let mut seen : NameSet := {}
  let mut boundary : NameSet := {}
  let mut project : Std.HashMap Name ConstantInfo := {}
  let mut pending := roots
  for n in roots do
    let some (.thmInfo _) := env.checked.get.find? n | throwError "Expected a theorem: {n}"
    let axioms ← collectAxioms n
    unless axioms.all standardAxioms.contains do
      throwError "Unexpected endpoint axiom at {n}: {axioms}"
    logInfo m!"ENDPOINT_AXIOMS {n} {axioms}"
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.checked.get.find? n | throwError "Missing declaration {n}"
    let some idx := env.getModuleIdxFor? n | throwError "Missing source owner for {n}"
    if !projectModule env.header.modules[idx.toNat]!.module then
      let axioms ← collectAxioms n
      unless axioms.all standardAxioms.contains do
        throwError "Unexpected axiom at external boundary {n}: {axioms}"
      boundary := boundary.insert n
      continue
    let owner := env.header.modules[idx.toNat]!.module
    if ([`PublicTheory, `PublicWilson, `ChallengeSpec] : List Name).contains owner then
      let some frozen := reference.checked.get.find? n | throwError "Public declaration missing in reference: {n}"
      unless frozen.type == ci.type && frozen.levelParams == ci.levelParams &&
          frozen.value? (allowOpaque := true) == ci.value? (allowOpaque := true) do
        throwError "Shared challenge declaration differs: {n}"
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial project dependency {n}"
    if ci matches .axiomInfo _ then throwError "Project axiom {n}"
    project := project.insert n ci
    pending := pending ++ ci.getUsedConstantsAsSet.toArray
    if let .inductInfo i := ci then pending := pending ++ i.all.toArray
  let externals := env.header.modules.filterMap fun m =>
    if projectModule m.module then none else some ({module := m.module} : Import)
  let base ← liftIO <| importModules externals {}
  for m in base.header.modules do
    if projectModule m.module then throwError "Project module in replay base: {m.module}"
  for n in roots do
    if (base.checked.get.find? n).isSome then throwError "Endpoint already in replay base: {n}"
  let mut replay := project
  let mut aliases := #[]
  for (n, ci) in project do
    if let some imported := base.checked.get.find? n then
      let .thmInfo original := imported | throwError "Non-theorem in replay base at {n}"
      let .thmInfo localProof := ci | throwError "Non-theorem project collision at {n}"
      unless localProof.levelParams == original.levelParams && localProof.type == original.type &&
          localProof.all == original.all do throwError "Duplicate theorem statement differs at {n}"
      let axioms ← withEnv base <| collectAxioms n
      unless axioms.all standardAxioms.contains do
        throwError "Unexpected axiom in external duplicate theorem {n}: {axioms}"
      let fresh := Name.str n "_boundedProofReplay"
      if (env.checked.get.find? fresh).isSome || (base.checked.get.find? fresh).isSome ||
          replay.contains fresh then throwError "Duplicate audit name already exists: {fresh}"
      replay := replay.insert fresh (.thmInfo {localProof with name := fresh, all := [fresh]})
      aliases := aliases.push fresh
      logInfo m!"DUPLICATE_THEOREM {n} axioms={axioms} checkedAs={fresh} type={localProof.type}"
  for n in boundary do
    unless (base.checked.get.find? n).isSome do throwError "Missing pinned external dependency: {n}"
  logInfo m!"REPLAY_START project={project.size} external={boundary.size}"
  liftIO <| IO.eprintln s!"Entering kernel replay with {project.size} project declarations and {aliases.size} checked duplicate aliases"
  let checked ← liftIO <| base.replay replay
  for n in roots ++ aliases do
    let some (.thmInfo verified) := checked.checked.get.find? n | throwError "Failed to replay {n}"
    let some (.thmInfo submitted) := replay[n]? | throwError "Missing submitted proof for {n}"
    unless verified.levelParams == submitted.levelParams && verified.type == submitted.type &&
        verified.value == submitted.value do throwError "Kernel proof differs from submission at {n}"
  logInfo m!"REPLAY_PASS project={project.size} external={boundary.size} endpoints={roots.size} duplicateAliases={aliases.size}"

end IndependentAudit

run_cmd do
  let manifest ← IO.FS.readFile "verification/joint-headlines.txt"
  let roots := (manifest.splitOn "\n").map (fun s => s.trimAscii.toString) |>.filter (· != "") |>.map String.toName
  if roots.isEmpty || roots.eraseDups.length != roots.length then throwError "Empty or duplicate headline"
  IndependentAudit.replayProofs roots.toArray
