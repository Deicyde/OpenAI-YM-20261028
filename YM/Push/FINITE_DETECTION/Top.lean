import Mathlib.Analysis.Calculus.TaylorIntegral
import YM.Push.FINITE_DETECTION.Pairs

/-!
# Top-coordinate criterion for the finite-rank-count input

Model the numerical part of  in the actual engineering/slot
grading and threshold of the hierarchy. The top projections of the principal
holonomy expressions on fixed homogeneous equation-family inputs (before top
t-weighting) may have higher weights at the SAME slot degree, plus bounded
higher slot degrees. Those same-slot terms need not be small after weighting.
Prove convergence to an *injective*, generally non-identity, triangular leading
map. Then one can use `matches_of_readout`. The hypotheses about the top
Wilson readouts, constraints and the matching budget stay hypotheses (no
lattice equation cylinders constructed). These tests are finite-dimensional
and before alignment; NOT error tolerances on the underlying hierarchy
required uniformly at all scales.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Top
open Function Set Filter Labels Extraction Dash Next.Extract RG
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {d : ℕ}




def threshold (C : Family G) (N : ℕ) := C.path.levels.clock.threshold N


















variable (U : Ideal C d →L[ℂ] C.label d)














end YM.Push.FiniteDetection.Top
