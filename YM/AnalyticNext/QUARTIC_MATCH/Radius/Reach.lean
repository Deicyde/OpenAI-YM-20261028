import YM.AnalyticNext.QUARTIC_MATCH.Radius.Spark

/-!
# Uniform implicit identity branch for actual tags
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open Purchase Articles Showroom Model Warp
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Orbit
section cost
variable (Q : Purchase) (G : Gauge) (r : ℝ)
def coupon := ColorCost G * Warp.debits Q G r
def reserve := min (thick Q G r) ((2:ℝ)⁻¹/(coupon Q G r * curvature Q G))
lemma positive (he : 0<r) : 0 < coupon Q G r := mul_pos (zero_lt_one.trans_le (color_ge G)) (spends Q G he)
lemma booked (he : 0<r) : 0 < reserve Q G r := lt_min (thicker Q G r he) (div_pos (by norm_num)
  (mul_pos (positive Q G r he) (zero_lt_one.trans_le (Warp.pays Q G))))

lemma down : reserve Q G r ≤ thick Q G r := min_le_left ..
lemma room : reserve Q G r < Q.width := (down Q G r).trans_lt (shorter ..)

def berth := min (reserve Q G r) ((reserve Q G r/4)/(coupon Q G r*Q.earnings 1))
lemma paid (he : 0<r) : 0<berth Q G r := lt_min (booked Q G r he) (div_pos (div_pos (booked Q G r he) (by norm_num))
    (mul_pos (positive Q G r he) (zero_lt_one.trans_le (Q.feesEarn _))))

lemma berth_paid : berth Q G r ≤ reserve Q G r := min_le_left ..
end cost
variable {c f : Side} (S : StepData c f) (H : Forest S.ratio) (p : Clip) {G : Gauge} (R : PathData G) (θ : S.Choices)
variable {F : Site f→ChartVars H G→ℝ} {Q : Purchase} {r : ℝ}
    (hp : Q.Applies H p R F) (hr : 0<r) (hh : PriceGap H p R r)
local notation "g" => GArray S H p R θ
local notation "a" => reserve Q G r
local notation "m" => Warp.bend S H p R θ

include hp hr hh






end Orbit
end YM.AnalyticNext.QuarticMatch.Radius
