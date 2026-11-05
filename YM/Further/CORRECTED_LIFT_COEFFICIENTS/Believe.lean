import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Deliver
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Growth
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Words

/-!
# The checkable gauge in schedule/chart/cov parameters

Loose enough to apply on long genuine paths, tight on actual p growth
from Wilson.band. In C's price convention. Demonstrate also b.h weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.MarginCost
open Filter Function Set Lattice Wilson Labels RG Cells Source Source.Drops
open Push.Uniform Work Push.Corrected Push.CutoffProjectors Growth Fund
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {d k N p t m l n s : ℕ} {C : Family G} {b : Series C}

structure Belongs (B : Screen C m p t) (Q : Copper G (C.side m p)) (R : ℝ) : Prop where
  room : 1 ≤ R
  size : (B.size:ℝ) ≤ R
  leg (i : Fin B.size) : ((B.leg i).walk.length:ℝ) ≤ R
  rate : B.rate ≤ R
  layout : (C.path.levels.params m).columns ≤ R
  stock (i j) : ‖Q.P i j‖ ≤ R



















-- Optional receipts before parameters chosen. These are monotone in R.


-- b_s^{(l)} cost in ℓ¹ on actual cutoff before grouping and
-- cochain/Wick read. -

end YM.Further.CorrectedLift.MarginCost
