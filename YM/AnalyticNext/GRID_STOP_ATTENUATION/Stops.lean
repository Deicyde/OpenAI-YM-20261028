import YM.AnalyticNext.GRID_STOP_ATTENUATION.Annual
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Budget


set_option warningAsError false

/-!
# Concrete stop & budget choices

Need calendar hypotheses (`Margins` and `Tabs`) for adopted history,
not just isBlock at each N.  commits h before both the k
requests and the word requests. Then we pick a common stop R for this h
and these finite degree data, before any l (admissible period or target
radius). The birth service can use its value but can't change any of
these choices for a finer k.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Planning
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Stock
open Push.GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Family G}

/- Thresholds independent of periods, from `Tabs`. Spot on ANY vertex
set. Also fits arbitrary other stage thresholds beyond a specified k0,
by choice of r. -/


/-- k-fork quote (independent of N,p). Flexible budgeting: q lower bound
on birth radii, and after forced divisor, c pays all three radial caps.
Can be post-block-dependent but buy the estimate `bear` on the k function
before roll. -/
structure Exchange where
  floor : ℕ → ℝ
  ceil : ℕ → ℝ
  positive k : 0 < floor k
  upper k : 0 ≤ ceil k

def Popular (C : Family G) (X : Exchange) := bear C (fun k => (1+8*X.ceil k)*(1+(X.floor k)⁻¹))



variable (C) (X : Exchange)

def budget (R : ℝ) (k : ℕ) :=
    1+Pair.principal C k R + (1+8*X.ceil k)*(1+(X.floor k)⁻¹)





variable {k h p : ℕ}

end YM.AnalyticNext.GridStop.Planning
