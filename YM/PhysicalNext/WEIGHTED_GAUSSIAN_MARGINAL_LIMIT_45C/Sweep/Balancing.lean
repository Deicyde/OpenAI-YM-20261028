import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Rounds

/-!
# Actually another comparison: remove the translation shift too

To test e.g. `d_1 Z` projection of the centered cloud WITHOUT the added
shift in normalized y. Translate the polynomial back on the SAME local
coordinates (no loss dependent on number of coordinates), compare from the
previous estimate, telescope at reference also. Need the sup shift already
*earned* in `Released`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
open Function Filter Set Finset MeasureTheory MvPolynomial
open Next.SectorChange.Gaussian
open Primitives.GCC.LocalPolynomial (Script)
open scoped Topology BigOperators Classical

variable {α β I : Type} [MeasurableSpace α] [MeasurableSpace β] [Fintype I]
variable {K D : ℕ} {E x : ℝ}
variable {μ : Measure α} {ν : Measure β} {Y W : α→ Vec I} {Z : β → Vec I} {δ : Vec I}

/-- Y common normalized source read, W source WITHOUT mean alignment,
Z common reference read (already unshifted). Laws from application; use
δ with this sign ONLY. -/
structure Released (K D : ℕ) (E x : ℝ) (μ : Measure α) (ν : Measure β) (Y W : α → Vec I) (Z : β → Vec I) (δ : Vec I) : Prop where
  collects : Collected K D E x μ ν Y Z
  shift z : Y z = δ + W z
  price : ‖δ‖ ≤ centerBill K E*speed x













end YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
