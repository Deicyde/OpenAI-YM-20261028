import YM.AnalyticNext.QUARTIC_MATCH.Radius.Warrant
import YM.AnalyticNext.QUARTIC_MATCH.Range

/-!
# High jets and true Taylor control

The low jets need not be **per anchor** equal when contracting against testing
vectors. Use agreement of the combined low jets; for the Taylor estimate on
the total, can still pay the higher derivatives by anchor-wise bounds:
sum over sites of *products* of weights, overlaps at physical separations
(and honest counting for degree zero). These aren't prices for separately
masked tile contributions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open Purchase  Showroom    
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

namespace Compiled
variable {c : Side} {G : Gauge}
variable {F F' : Site c→Dir G c→ℝ} {f g : Dir G c→ℝ}

/-- Can pay `GermPage` at each degree with the corresponding signed velocity
rate, even if not uniformly bounded analytic norm across r. -/
structure GermPage (ρ : ℝ) (k : ℕ) (f : Dir G c→ℝ) (F : Site c → Dir G c→ℝ) (t C : ℝ) : Prop where
    pos : 0<ρ
    paid : 0<t
    fees : 0 ≤ C
    equality {x : Dir G c} : ‖x‖<ρ → f x=∑ i,F i x
    atX {x : Dir G c} : ‖x‖<ρ → ∀ i,ContDiffAt ℝ ω (F i) x
    funds {x : Dir G c} : ‖x‖<ρ → ∀ i j,j ≤ k → Costs (Fetch.trials G t i) (budget ℝ) (F i) x j C

variable {r r' ρ t u D C : ℝ} {k m j : ℕ} {x : Dir G c} (h : GermPage r k f F t C)
include h










end Compiled
end YM.AnalyticNext.QuarticMatch.Radius
