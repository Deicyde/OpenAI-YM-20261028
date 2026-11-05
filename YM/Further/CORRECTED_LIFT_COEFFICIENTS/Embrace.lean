import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Orbit
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Symbol

/-!
# One operationally signed supplier to the calibration gate
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Compass
open Filter Function Set Lattice Wilson RG Source Source.Drops Labels Cells Extraction
open Push.Corrected Push.Corrected.Issue Push.CutoffProjectors Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {C : Family G} {m p d N t : ℕ} (B : Screen C m p t)
  (c : ∀ s, vacancy B s) (Q : Copper G (C.side m p))

def adjunct : Portfolio C m p t := ⟨fun s => arrow B s (c s), Q⟩

-- Data at h-tier before projector/Weak estimates. Includes all colors and
-- paths, one and same Q. Supply nonuniform tubes separately.

end YM.Further.CorrectedLift.Compass
