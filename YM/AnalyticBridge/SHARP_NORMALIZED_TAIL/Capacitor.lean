import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian

/-!
# Trace-sized bill for Gaussian Lᵖ tests

For a common marginal. Proof shortcut for the quadratic moment:
linearize against auxiliary iid gaussianReal and use *both* linear mgf's.
Requires only a spectral upper price. Zero rates and empty dimensions
allowed. Don't use real integrals on unverified multipliers (esp. smallness
of the envelope refers to the SUM over all simultaneous uses).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Capacitor
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Finset
open Next.SectorChange.Gaussian
open scoped Topology BigOperators MatrixOrder ENNReal Classical

variable {J : Type} [Fintype J] [DecidableEq J]









def Cap (K : ℝ) (C : Table J) := ∀ u : Vec J,u ⬝ᵥ (C *ᵥ u) ≤ K*(u ⬝ᵥ u)

def power (w z : Vec J) := ∑ i,w i*z i^2


end YM.AnalyticBridge.Sharp.Capacitor
