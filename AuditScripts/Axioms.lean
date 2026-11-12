import Audit.Reduction.Main
import Audit.BlindFamily
import Audit.Repair.F1

/-! Axiom check for the audit's main results: each should report only
`propext`, `Classical.choice` and `Quot.sound`. Run with `lake env lean AuditScripts/Axioms.lean`. -/
#print axioms YMAudit.jointExistence_of_continuum
#print axioms YMAudit.wilson_clause_redundant
#print axioms AuditDemo.blind_regular
#print axioms YMAudit.F1.reduced_not_perCharacter
#print axioms YMAudit.F1.zeroWord_const
#print axioms YMAudit.F1.jointExistence_of_F1
