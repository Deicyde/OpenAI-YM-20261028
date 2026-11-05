import YM.AnalyticNext.GRID_STOP_ATTENUATION.Pair

set_option warningAsError false

/-!
# Pricing the intermediate translated singleton Pulses, with support reserve
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Pair
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi
open Push.GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n : Side} {C : Family G} {d k m p N : ℕ}

-- use `Multi.BranchOne.costs` literally at higher budget; changed Rep fields
-- other than p never appear in cost


variable (B : Probe C N p d k) (v : C.label d) (φ : ℕ → ℝ) (H : C.Makes)
variable (hB : B.Based C.params (C.localSection d) (C.ref d)) (hk : k≤N)



def pulse (i : ℕ) (o : Site (C.side i p)) : Pulse G (C.side i p) :=
  AxisShift.carry o (BranchOne.center (split B i v) (C.localSection d) 0 (C.path.rep N p i))

include H hB hk





/-- Multiplier from voice cost to Pulse cost. Commits to one reserve,
which is to be RECOVERED afresh at each use if nonzero. No power of
inverse theta needed for this particular Credit (mask boundary derivatives
use true P.p prices). -/
def currency (A : Levels G) (δ : ℝ) (i : ℕ) := Real.exp ((A.params i).supportExponent + δ) * (A.params i).columns

omit H hB hk in
lemma currency_one (A : Levels G) (δ : ℝ) (i) (h : 0 ≤ δ) : 1 ≤ currency A δ i :=
  one_le_mul_of_one_le_of_one_le (Real.one_le_exp (add_nonneg (A.params i).price_pos.le h)) (A.params i).columns_ge


end YM.AnalyticNext.GridStop.Pair
