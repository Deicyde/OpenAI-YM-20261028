import YM.Org.Theatre
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.OnTrack
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian
/-! # Actual limit covariance evaluation

Only a tool: pure real Gaussian, before attaching to Wilson integral.
Derivatives here STILL x in all given x-horizontal directions, analytic
kernel selection but no analytic continuation of e.g. domain predicates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open MeasureTheory Function Filter Set Metric Next.SectorChange.Gaussian
open scoped Topology BigOperators ContDiff
variable {I : Type} [Fintype I] (Q : ℝ × Vec I → ℝ)

def pureMass (t : ℝ) (y : Vec I) := Real.exp (-spot Q t y)
def wind₁ (t : ℝ) (y : Vec I) := pureMass Q t y * (-spot (horizontal Q) t y)
def wind₂ (t : ℝ) (y : Vec I) := pureMass Q t y * ((spot (horizontal Q) t y)^2 - spot (horizontal (horizontal Q)) t y)

variable {t : ℝ}
private lemma fixed (hf : ContDiffAt ℝ ω Q (t,0)) (y : Vec I) : ContDiffAt ℝ ω (fun t => spot Q t y) t := by
  unfold spot; exact (((Bends_diff hf).clm_apply contDiffAt_const).clm_apply contDiffAt_const).div_const _
private lemma first (hf : ContDiffAt ℝ ω Q (t,0)) (y : Vec I) : HasDerivAt (fun t => pureMass Q t y) (wind₁ Q t y) t :=
  (((spot_raise y hf) ▸ ((fixed Q hf y).differentiableAt (by simp)).hasDerivAt).neg.exp)
private lemma second (hf : ContDiffAt ℝ ω Q (t,0)) (y : Vec I) : HasDerivAt (fun t => wind₁ Q t y) (wind₂ Q t y) t := by
  have he : HasDerivAt (fun t => spot (horizontal Q) t y) (spot (horizontal (horizontal Q)) t y) t :=
    (spot_raise y (horizontal_diff hf)) ▸ ((fixed _ (horizontal_diff hf) y).differentiableAt (by simp)).hasDerivAt
  convert! ((first Q hf y).mul he.neg) using 1
  unfold wind₁ wind₂; simp only [Pi.neg_apply]; ring


end YM.PhysicalNext.FlatResponse
