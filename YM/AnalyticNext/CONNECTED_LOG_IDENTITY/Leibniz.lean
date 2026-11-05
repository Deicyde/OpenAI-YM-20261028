import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Fuels
import YM.Work.A05.Read
import YM.Work.A07

set_option warningAsError false

/-!
# Left-link jets of products at a single healthy support

Work ONLY with the increment germ, so also valid at equality on the
flag cutoff. Important not to try applying Healthy assumptions
also along a neighboring $t\ne0$ without proving germ persistence
of each claimed identity. Implement the ordered product rule by a
finite binary recurrence on lists (preserves order of positions).
Real vacuum labels.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Jets
open Lattice RG Wilson MeasureTheory Filter Function Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n : Side} {G : Gauge}
abbrev D (G : Gauge) (n : Side) := Directions G n
abbrev germ (k : ℕ) (U : Config G n) (F : Config G n → ℝ) :=
  ContDiffAt ℝ (k : WithTop ℕ∞) (F ∘ increment U) 0

variable {k : ℕ} {F H : Config G n → ℝ} {U : Config G n}







section Lists
variable {α : Type*}

/-- linear allotment operator over selections of ordered positions. -/
def allot (l : List α) (f : List α → List α → ℝ) : ℝ := match l with
  | [] => f [] []
  | i::s => allot s (fun u v => f (i::u) v + f u (i::v))








end Lists



/-- Point-jet test with the cost rate r per derivation. -/
def budget (U : Config G n) (k : ℕ) (Q : D G n → Prop) (F : Config G n → ℝ) (c r : ℝ) :=
  germ k U F ∧ ∀ l : List (D G n), l.length ≤ k → (∀ i∈l,Q i) → ‖leftDerivs F l U‖ ≤ c*r^l.length










end YM.Push.LogIdentity.Jets
