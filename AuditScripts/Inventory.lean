import ChallengeSpec
import Lean
open Lean Elab Command

/- Inventory of every constant introduced by the three trusted modules, with kind and
whether it is reachable from `YangMills.JointExistence` (types and values, transitively). -/
run_cmd do
  let env ← getEnv
  let trusted : List Name := [`PublicTheory, `PublicWilson, `ChallengeSpec]
  let owner (n : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if trusted.contains m then some m else none
  -- reachability
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`YangMills.JointExistence]
  while !todo.isEmpty do
    let n := todo.back!; todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      if (owner n).isSome || n == `YangMills.JointExistence then
        todo := todo ++ ci.getUsedConstantsAsSet.toArray
        if let .inductInfo i := ci then todo := todo ++ i.ctors.toArray
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some m := owner n | continue
    let kind := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "AXIOM"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "structure/inductive"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
    let auto := n.isInternal || (match n with | .str _ s => s ∈ ["rec","recOn","casesOn","noConfusion","noConfusionType","mk","ext","ext_iff","inj","injEq","sizeOf_spec","mk.injEq","brecOn","below"] || s.startsWith "_" || s.startsWith "eq_" || s.startsWith "proof_" | _ => false)
    let reach := if seen.contains n then "reached" else "-"
    rows := rows.push s!"{m}\t{kind}\t{if auto then "auto" else "user"}\t{reach}\t{n}"
  let sorted := rows.qsort (· < ·)
  IO.FS.writeFile "Audit/inventory.tsv" (String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"rows={sorted.size}"
