import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Polynomial

/-!
# Compose polynomial tests in their same coefficient currency

For growing stencils (number of *variables* growing, not degree!). No
conversion of norms across dimensions without price. Composition paid
from true coefficients and the counted local substitutions. In particular
translation estimate in `translate_budget` will pay a *factor* of the sup
shift for testing the difference, important at large x when passing to
centered-only curvature laws (those are different coordinates from the
common y in `Readout`).
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
open Function Finset MvPolynomial
open Next.SectorChange.Gaussian
open Primitives.GCC.LocalPolynomial (Script Key key_length length)
open scoped Topology BigOperators Classical

section fees

variable {I J : Type}



















variable [Fintype I]
-- GCC multiplicity convention (`Key`), rather than suppress repeated occurrences.



variable {d : ℕ} (P : Script I) (hd : P.totalDegree ≤ d)
include hd





end fees

section shift
variable {I : Type}





variable [Fintype I]

end shift

section matrix
open Matrix
variable {I J : Type} [Fintype J]

/-- Also useful with real common b != 0 (price explicitly). -/
def affineInputs (A : Matrix I J ℝ) (b : Vec I) (i : I) : Script J :=
    C (b i:ℂ)+∑ j : J, C (A i j:ℂ)*X j

def pullPoly (A : Matrix I J ℝ) (b : Vec I) (P : Script I) : Script J := aeval (affineInputs A b) P
lemma peval_pulled (A : Matrix I J ℝ) (b : Vec I) (z : Vec J) (P : Script I) :
    peval (pullPoly A b P) z = peval P (b+A *ᵥ z) := by
  unfold peval pullPoly; erw [aeval_bind₁]; simp [affineInputs,mulVec,dotProduct]

variable [Fintype I]

end matrix
end YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
