import YM.AnalyticNext.QUARTIC_MATCH.Radius.Articles
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Stocks

/-!
# True post-L remainders. Some hit-style corollaries

All directional mixed, duplicates including. Does not price local guards. This
is global in the REAL sup neighborhood, with exponential link sensitivity in native
units. Valid even if there are finitely many local path conventions at repeated slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open Purchase Articles Showroom Model   
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Compiled
open Green (wt)
variable {c : Side} {G : Gauge}
variable {F F' : Site c→Dir G c→ℝ} {f g : Dir G c→ℝ}
variable {r r' ρ t u D C : ℝ} {k m j : ℕ} {x : Dir G c}
variable (h : GermPage r k f F t C) (hm : m≤k) (hz : ∀ i : ℕ,i < m → iteratedFDeriv ℝ i f 0=0)
include h hm hz


section overlap
omit h hm hz

def strip (t : ℝ) (m : ℕ) := t/(m+2:ℝ)





abbrev stick (b : Body 1 c) (x : G.Color) : Dir G c := Pi.single b x

end overlap


end Compiled
end YM.AnalyticNext.QuarticMatch.Radius
