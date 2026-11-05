import YM.AnalyticNext.QUARTIC_MATCH.Radius.Response
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Scene

/-!
# Hit budgets on every smooth branch component

Uniform predictions. Need all sym Hess permissions on the same purchase; all
spending after the length. Earnings cost every real point in the basin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open Purchase Articles Showroom Model Warp Raised Orbit
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

namespace Managed
open Green (wt address)
section costs
variable (Q : Purchase) (G : Gauge) (η : ℝ)

def splitB (m) := min (min (lease Q G η) (Q.rates m)) (Q.vacancy m) / (m+1:ℝ)
lemma meets (he : 0<η) (m) : 0<splitB Q G η m := by
  unfold splitB; exact div_pos (lt_min (lt_min (lease_pos Q G he) (Q.rate _)) (Q.vacant m)) (by positivity)


def critFee (m : ℕ) (k : ℕ) (A : ℝ) := Radius.expected k (Q.earnings m) A + Q.earnings m


/-- Covers arc derivatives. -/
def bought (m : ℕ) : ℕ → ℝ
  | 0 => 1
  | i+1 => max (bought m i) (coupon Q G η * critFee Q m i (bought m i))

end costs
variable {G : Gauge} {c f : Side} (S : StepData c f) (H : Forest S.ratio) (p : Clip) (R : PathData G)
variable {F : Site f → ChartVars H G → ℝ} {Q : Purchase} {η : ℝ} (hp : Q.Applies H p R F) (hr : 0 < η) (hh : PriceGap H p R η)
variable {χ : Dir G c → AxisChart G H} (hk : Reaches Q η S H p R χ)
variable {x : Dir G c} (he : ‖x‖ < Orbit.berth Q G η)
local notation "z" => arc χ x
include he hk
omit hr hh hp in
lemma tangent_chart (i : ℕ) (d : Fin i→Dir G c) :
    iteratedFDeriv ℝ i (arc χ) x d=(iteratedFDeriv ℝ i (fun x : Dir G c=>x) x d,iteratedFDeriv ℝ i χ x d) := by
  have ht : ContDiffAt ℝ ω (arc χ) x := contDiffAt_id.prodMk (hk.smooth x he)
  exact Prod.ext (DFunLike.congr_fun ((ContinuousLinearMap.fst ℝ (Dir G c) (AxisChart G H)).iteratedFDeriv_comp_left ht le_top) d).symm
    (DFunLike.congr_fun ((ContinuousLinearMap.snd ℝ (Dir G c) (AxisChart G H)).iteratedFDeriv_comp_left ht le_top) d).symm
variable {j m : ℕ} {C t : ℝ} (hc : 1≤C) (hm : j+1≤m) (hu : 0≤t) (hv : t ≤ splitB Q G η m)

omit he hk in
lemma identity_price (d : Site f) (t : ℝ) (s : ℝ) (ht : t ≤ s) (m) (he : 1 ≤ C) (hm : 0 < m) :
    Costs (outer S G t d) (outer S G s d) (id : Dir G c→ Dir G c) x m C := by
  intro w b hb
  let A := ContinuousLinearMap.id ℝ (Dir G c)
  have h : 0 ≤ C*∏ i,b i := mul_nonneg (zero_le_one.trans he) (Finset.prod_nonneg fun i _=> (hb i).1)
  change outer S G s d (iteratedFDeriv ℝ m (⇑A) x w) _
  obtain hm|hm := eq_or_lt_of_le (show 1 ≤ m from hm)
  · subst m; rw [iteratedFDeriv_one_apply,A.fderiv,Fin.prod_univ_one]
    exact Amount.elevate (seek ht (hb 0).1 (hb 0).2) (le_mul_of_one_le_left (hb 0).1 he)
  rw [Polish.fading A x m hm,_root_.zero_apply]; exact Fetch.zeroed _ _ _ _ h
include hp hr hv hc hm

section pace
include hu hh
omit hc hm

end pace
end Managed
end YM.AnalyticNext.QuarticMatch.Radius
