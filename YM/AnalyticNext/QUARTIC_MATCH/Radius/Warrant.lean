import YM.AnalyticNext.QUARTIC_MATCH.Delivery
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Display

/-!
# Extending the real estimates over working widths
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
open  Showroom 

variable {G : Gauge}
structure Purchase where
  width : ℝ
  pos : 0 < width
  rates : ℕ→ℝ
  rate k : 0<rates k
  fees : ℕ→ℝ
  cost k : 1 ≤ fees k

namespace Purchase
variable {c f : Side} {S : StepData c f} (Q : Purchase) (H : Forest S.ratio) (p : Clip) (R : PathData G)
structure Applies (F : Site f → ChartVars H G → ℝ) : Prop where
  formula {x : ChartVars H G} : ‖x‖ < Q.width → ∀ θ : S.Choices, uncurry (tested H θ p R) x= ∑ i,F i x
  smooth {x : ChartVars H G} : ‖x‖ < Q.width → ∀ i, ContDiffAt ℝ ω (F i) x
  stamps {x : ChartVars H G} : ‖x‖ < Q.width → ∀ i k m,k ≤ m → Costs (On S H G (Q.rates m) i) (budget ℝ) (F i) x k (Q.fees m)
  frame {x : ChartVars H G} : ‖x‖ < Q.width → ∀ (i : Edge (Site c)) (θ : S.Choices),
    S.patch.usesMin S.kernel (expandAt (S.ratio.embed i.1) (live H x)) ∧ S.patch.usesBest S.kernel (S.connector (live H x) θ.1 i)
end Purchase
variable (P : Patch) (K : KernelChoices) (hk : P.Branches K G) (p : Clip) (σ C : ℝ) (hσ : 0<σ)
include hk hσ

end YM.AnalyticNext.QuarticMatch.Radius
