import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Spool



/-!
# Path lengths and all jet slots

Absolute counting bounds on the real nonlinear plaquette data in the actual D,
not requested kernel regularity past a flag decision. Whole Wilson paths in
all Ad factors (V hit also there in this estimate). Allocate only a fraction
of the length width to the derivative caps, leaving room for the kernel
rates and counts. No operator sup at the precision input assembled from a
color equivalence in (growing) volume with unestimated norms.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Function Lattice RG Pressure Precision Wilson Tree 
open Next.SectorChange 
 
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

def pulsePath (S : StepData c f) (V : Config G c) (s : Signed) (q : Site f)
    (A : Directions G f) (u : RG.Slot) := G.adjoint (travel (facade S s V 0) q u.walk)
      (plaquetteJet S V s (Work.F03.slotFace u q) A)

-- fixed norms at G
















lemma face_series (V : Config G c) (s : Signed) (T : Tube G S)
    (x : ℝ) (a : Directions G f) (p : Cell f) {o : Clip} {σ C Λ : ℝ} (hT : T.up.Bounds o σ C Λ) :
    Rows.faceKick T x V a s (p,true) = ∑ u ∈ spool (Stores.till x),
      condensed T.up p.2 u • pulsePath S V s p.1 a u := by
  simp only [Rows.faceKick,↓reduceIte,barrel_on_spool T.up hT]; rfl

end YM.AnalyticBridge.NonflatCovarianceLocality
