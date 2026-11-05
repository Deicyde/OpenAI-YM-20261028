import YM.Bid.Fuels
import YM.Next.WARD_BIN.Printing
import YM.Org.Input

/-!
# RDuets at actually different blocking offsets

We'll need canonical cones at such offsets. Don't infer Fits/calibration
from centered C.factory. Give kit-derived top (on this mask!) a cost before
applying one-step RPaper estimate at these locations. Same flag merge, tested
through *all* derivative orders of this step. Cost based on core only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Lattice Wilson RG Source Gas Work.G07 Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {H : Hol G} {n : Side} {T : Support n}
variable (C : SectionData F) {c w k σ K Λ v κ' : ℝ} {R : Rep G n} (D : Pad R.activities R.p)
  {S : Finset Cover} {o : Site n} {i : ℕ}

def pennies (C : SectionData F) (D : Pad R.activities R.p) (S : Finset Cover) (o : Site n) (i : ℕ) :
    F.Coeff →ₗ[ℂ] Baton F n := IsLinearMap.mk' (fun x => kit C S i o D (canonical C R.p.threshold x) (primary F R.p.threshold x))
    (kit_linear (F.coords.symm.toLinearMap ∘ₗ F.scaled R.p.threshold⁻¹) (IsLinearMap.mk' _ (canonical_linear C R.p.threshold)) C S i o D)






end YM.WardBin
