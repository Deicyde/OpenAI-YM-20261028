import YM.AnalyticNext.QUARTIC_MATCH.Radius.Amenities
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Stocks

/-!
# Releasing those post-L grants for a path and solve

On true unmasked formulas. The controlled representative is not a new
critical *germ*. Use the whole Present package, not choosing a different
prescription when probing the derivatives. Doesn't charge clipping (or
fluctuations). Consumer in schedule follows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open Purchase Articles Showroom Model Warp Raised Orbit Managed Compiled Aisle
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

namespace Fruits
structure Stock (G : Gauge) where
  Q : Purchase
  width : ℝ
  pos : 0 < width
  rates : ℕ→ ℝ
  rate k : 0 < rates k
  prices : ℕ→ℝ
  fees k : 1 ≤ prices k

def rigs (G : Gauge) (Q : Purchase) (η : ℝ) (he : 0<η) (l : Side) (q : Clip) (τ D : ℝ) (hτ : 0<τ) : Stock G where
  Q := Q
  width := min 1 (berth Q G η)
  pos := lt_min zero_lt_one (Orbit.paid Q G η he)
  rates k := min (splitB Q G η k*l.val) (Estimate.down τ k)
  rate k := lt_min (mul_pos (meets Q G η he k) (by positivity : 0 < (l.val:ℝ))) (Estimate.down_pos k hτ)
  prices m := presented l (splitB Q G η m) m (marked Q G η m)+max 1 (Fetch.dues G τ D q m)
  fees m := le_trans (enough l (meets Q G η he m).le m (marked_ge ..)) (le_add_of_nonneg_right (zero_le_one.trans (le_max_left ..)))

section release
variable {c f : Side} (S : StepData c f) {G : Gauge} (p q : Clip) (W T : PathData G) (H : Forest S.ratio)
    {σ τ C B η Λ Ξ : ℝ}

/-- Difference here vs any path within this budget, before even checking
matching. Per-tile parcel can use different anchor extension outside balls.
χ uses actual stationarity graph for ALL orientations. Payments
exposed. Low-order zeros precisely from purchased matching. -/
structure Pays (K : Stock G) (η : ℝ) (S : StepData c f) (H : Forest S.ratio) (R T : PathData G) (p q : Clip)
    (ρ χ : Dir G c → AxisChart G H) (E : Site c → Dir G c → ℝ) : Prop where
  hood : K.width ≤ berth K.Q G η
  source : ∃ F, K.Q.Applies H p R F ∧ E=Aisle.residence S H F χ-Rotate.byStage q T
  same : χ =ᶠ[𝓝 0] ρ
  reaches : Raised.Reaches K.Q η S H p R χ
  station x : ‖x‖<K.width → ∀ θ : S.Choices, HasFDerivAt (tested H θ p R x) (0 : AxisChart G H →L[ℝ] ℝ) (χ x)
  goods θ k : GermPage K.width k (Joint.value H θ p R χ-Residual.baseAt q T) E (K.rates k) (K.prices k)


end release


end Fruits
end YM.AnalyticNext.QuarticMatch.Radius
