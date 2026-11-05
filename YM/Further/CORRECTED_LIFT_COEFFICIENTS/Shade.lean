import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Deliver
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Words
/-!
# G-invariance certificate, calibrated source matrix respects ordinary reality
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Compass
open Filter Function Set Lattice Wilson RG Source Source.Drops Labels Cells Extraction
open Push.Corrected Push.Corrected.Issue Push.CutoffProjectors Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {C : Family G} {d m p t l N : ℕ} {B F : Screen C m p t}
  {Q : Copper G (C.side m p)}



/-- Full color convention on Wick covariance, no complex entry-wise Ad
on a pair of real plaquettes. -/
def isotropic (Q : Copper G (C.side m p)) : Prop := ∃ P : Face (Per (C.side m p))→ Face (Per (C.side m p))→ℝ,
    ∀ a b, Q.P a b = if a.2=b.2 then P a.1 b.1 else 0















structure TrueStar (C : Family G) (d m N p : ℕ) : Prop where
  natural v : primary C (d:=d) (star v) m N p=star (primary C v m N p)
  repeated : ∃ s : Equiv.Perm ℕ, ∀ i, (short C d m N p i ↔ short C d m N p (s i)) ∧
      ∀ v : C.label d, short C d m N p i → annal C (star v) m N p (s i) = star (annal C v m N p i)






end YM.Further.CorrectedLift.Compass
