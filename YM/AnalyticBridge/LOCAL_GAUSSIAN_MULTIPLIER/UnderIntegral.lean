import YM.Next.EXTRACTION.Base
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Sides
import YM.Work.A15
import YM.Work.C01


/-!
# Domination at an open germ, to pair with the multiplier budgets

In addition to ordered values computed under the integral sign, need
actual chart regularity (e.g., to later commission unmasked functions).
Prove it for B70 link increments; suffice *left* jet domination. Thus
clients needn't incur yet another dictionary of estimates for derivatives
within displacement charts with moving gauge. No change of sigma-finite
laws inside `Study` here (if varying C use the FKer replacement on
a neighborhood before calling).
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian.Integral
open Function Filter Set Lattice Wilson RG ProjectorNext.Equivariance Next.Foundations
open MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}
section center
variable {U : Config G n} {v w : Directions G n} {f : Config G n → ℝ}






















-- Chart derivative identity of the *kernel*, retaining the recentering CLM.

end center

variable {S : Set (Config G n)} {P : Type*} [MeasurableSpace P] {F : P → Config G n → ℝ}
variable {μ : Measure P} {k : ℕ}

/-- S can be arbitrarily small, but applies across this entire product
integrand and all its variables. Need domination in THIS fixed measure. -/
structure Study (μ : Measure P) (S : Set (Config G n)) (k : ℕ) (F : P → Config G n → ℝ) : Prop where
  clearing : IsOpen S
  borel (x : Config G n) : x∈S → Measurable (fun p => F p x)
  clean (p) (x) : x∈S → HasOrderAt (F p) x k
  controlled (l : List (Directions G n)) : l.length ≤ k → ∃ f : P → ℝ, Integrable f μ ∧
    ∀ p U, U ∈ S → ‖leftDerivs (F p) l U‖ ≤ f p



namespace Study
variable {U : Config G n} {l : List (Directions G n)}
















end Study
end YM.AnalyticBridge.LocalGaussian.Integral
