import YM.Further.FREE_COVARIANCE_KP.KP.Field
import YM.Further.FREE_COVARIANCE_KP.KP.Growth

/-! # Regulated continuum read to normalized kernel on the lag. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Exterior Lattice Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace

abbrev PA := PlaqAxes




-- (-1)^B.length uses ℝ



structure Matches (n : ℕ) (f:E4→ℂ) (g:E4→ℝ) : Prop where
  serves : Profit f
  rate : ∃ C:ℝ, 0≤C ∧ ∀ x:E4, 1≤‖x‖ → ‖retract f x-↑(g x)‖ ≤ C*(‖x‖^n)⁻¹
namespace Matches
variable {n : ℕ} {f f' : E4→ℂ} {g g' : E4→ℝ}





end Matches

-- combine heads into identical template on the two sides












end YM.Further.FreeCovariance.KP
