import YM.Extra.ITERATION_NO_LOSS.Gates
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Bills

/-!
# Savings for single polynomial probes whose support may fill a stencil

An account at fixed K0 (= what was bought at the sparse service; will be
independent of the dimension of Y here). Keep each coordinate tail separate,
then pay linear, not exponential, in the dimension of Y (possibly growing
with x) to drop a joint cube guard. NO estimate on `exp(c * energy Y)` with
this currency. Here even the second-power payment for the polynomial uses no
factor of number of coordinates. These are full actual measure tests, not
statements about complete support qualification of a factor for a further
polymer calculation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
open Function Filter Set MeasureTheory Finset
open Next.SectorChange.Gaussian
open scoped Topology BigOperators Classical

variable {α I J : Type} [MeasurableSpace α]

/-- Coordinate tail account. Y is the (possibly large-dimensional) joint
local read in normalized comparison coordinates. Bound uses the SAME M at
every coord. -/
structure Savings (K : ℕ) (E M : ℝ) (μ : Measure α) (Y : α → Vec I) (f : α → ℂ) : Prop where
  nonneg : 0 ≤ M
  borel : Measurable f
  measure_Y : Measurable Y
  first : Integrable f μ
  first_norm : (∫ z,‖f z‖ ∂μ) ≤ M * kiln K E
  second : Integrable (fun z => ‖f z‖^2) μ
  second_bound : (∫ z, ‖f z‖^2 ∂μ) ≤ M^2*kiln K E
  tail (i : I) (R : ℝ) (hR : 0 ≤ R) (s : Set α) (hs : MeasurableSet s) (ht : ∀ z∈s,R ≤ |Y z i|) :
    (∫ z in s, ‖f z‖ ∂μ) ≤ M * kiln K E * Real.exp (-reserve K E*R^2)

variable {K : ℕ} {E M : ℝ} {Y : α → Vec I} {μ : Measure α} {f : α → ℂ}









section cube
variable [Fintype I]


end cube
end YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
