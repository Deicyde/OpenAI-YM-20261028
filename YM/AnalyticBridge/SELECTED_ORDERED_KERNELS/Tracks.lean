import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Inverse

/-!
# The ordinary path-row *input* on a uniform ball

Extends the TrackBill/PathsAffine price argument to nonzero B: the already
verified uniform ceiling for proof regularizations now applies on a common
open ball (uniform over reads!). The locality lemma is made on translated
functions with the perturbation only chopped. Keep the elbow prices and tail
gain on each label, never using a summed short-stencil hypothesis.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Small
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 Filter Function Set Metric
  FreeResolvent Affine TestD Mark
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c n : Side} {S : StepData c f} {k : ℕ} {σ γ M d : ℝ}
  {b : Vec G c 1}

lemma small_sleeve (hb : ‖b‖ ≤ (filePrice G)⁻¹) (i) : sleeve G (decode b i)=decode b i := by
  have he := file_pos G
  have hp : ‖file (G:=G) 1 i b‖ ≤ 1 := ((file 1 i).le_opNorm b).trans ((mul_le_mul (folder ..) hb (norm_nonneg _)
    (zero_le_one.trans he)).trans (mul_inv_cancel₀ (zero_lt_one.trans_le he).ne').le)
  change ‖decode b i‖ ≤ 1 at hp
  rw [sleeve, (cuff G).one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hp), one_smul]

variable (hb : ‖b‖ < (filePrice G)⁻¹)
include hb







variable {W : PathData G} (hs : 0 < σ) (hW : Sheet W σ M) (S : StepData c f) (s : Signed)
include hs hW





omit hs hW







end YM.SelectedOrderedKernels.Small
