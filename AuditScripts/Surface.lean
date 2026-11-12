import ChallengeSpec
import Lean
open Lean Elab Command Meta

/- Classify the trusted surface: structures (with fields), top-level definitions, instances,
   and whether each is reachable from `YangMills.JointExistence`. -/
run_cmd do
  let env ← getEnv
  let trusted : List Name := [`PublicTheory, `PublicWilson, `ChallengeSpec]
  let owner (n : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if trusted.contains m then some m else none
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`YangMills.JointExistence]
  while !todo.isEmpty do
    let n := todo.back!; todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      if (owner n).isSome then
        todo := todo ++ ci.getUsedConstantsAsSet.toArray
        if let .inductInfo i := ci then todo := todo ++ i.ctors.toArray
  let mut structs : Array String := #[]
  let mut defs : Array String := #[]
  let mut insts : Array String := #[]
  let mut nFields := 0
  for (n, ci) in env.constants.toList do
    let some m := owner n | continue
    if n.isInternal then continue
    let r := if seen.contains n then "reached" else "UNREACHED"
    if isStructure env n then
      let fs := getStructureFields env n
      let isProp ← liftTermElabM <| do
        let t ← inferType (mkConst n (ci.levelParams.map mkLevelParam))
        return (← forallTelescope t fun _ b => pure b.isProp)
      nFields := nFields + fs.size
      structs := structs.push s!"{m}\t{n}\t{if isProp then "Prop" else "data"}\t{fs.size} fields\t{r}\t{fs.toList}"
    else if (env.getProjectionFnInfo? n).isSome then
      continue
    else if isInstanceCore env n then
      insts := insts.push s!"{m}\t{n}\t{r}"
    else if let .defnInfo _ := ci then
      if (← liftTermElabM <| Meta.isMatcher n) then continue
      let s := toString n
      if s.endsWith ".mk" || (s.splitOn "._").length > 1 then continue
      if (n.components.getLast!.toString).startsWith "eq_" then continue
      defs := defs.push s!"{m}\t{n}\t{r}"
  IO.FS.writeFile "Audit/surface.txt" (String.intercalate "\n" (
    ["## structures"] ++ (structs.qsort (· < ·)).toList ++ ["## definitions"] ++ (defs.qsort (· < ·)).toList ++
    ["## instances"] ++ (insts.qsort (· < ·)).toList) ++ "\n")
  logInfo m!"structures={structs.size} (fields total {nFields}) defs={defs.size} instances={insts.size}"
