import YM
import Lean
set_option autoImplicit false
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let all := env.checked.get.constants.fold (init := (#[] : Array Name)) (fun xs n _ =>
    match env.getModuleIdxFor? n with
    | none => xs
    | some idx =>
      if Name.isPrefixOf `YM env.header.modules[idx.toNat]!.module then xs.push n else xs)
  let mut holes := 0
  let mut axs := 0
  for n in all do
    let some ci := env.checked.get.find? n | throwError "Missing declaration {n}"
    if ci.getUsedConstantsAsSet.contains `sorryAx then
      holes := holes + 1
      liftIO <| IO.println s!"PLACEHOLDER {n}"
    if ci matches .axiomInfo _ then
      axs := axs + 1
      liftIO <| IO.println s!"PROJECT_AXIOM {n}"
  liftIO <| IO.println s!"DECLARATION_SCAN declarations={all.size} directSorryAx={holes} projectAxioms={axs}"
  unless holes == 0 && axs == 0 do throwError "Project contains a placeholder or a new axiom"
  for n in [`YM.Pert.Position.Mode, `YM.Pert.Position.solvesJets, `YM.Pert.Position.jets_join,
      `YM.Pert.Position.stageTarget, `YM.SharpGram.FixedPrice, `YM.SharpGram.DynamicalCost,
      `YM.OPE.Log.MatrixTicket, `YM.OPE.LogTrace, `YM.OPE.tickets_suffice] do
    if (env.checked.get.find? n).isSome then throwError "Unexpected declaration {n}"
  logInfo "INVENTORY_PASS"
