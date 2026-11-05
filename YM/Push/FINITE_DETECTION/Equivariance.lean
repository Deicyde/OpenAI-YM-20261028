import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Work.A05.Read
import YM.Work.A07

/-!
# Real/hypercubic module type of the quotient

For E near  and . Need ALSO an intertwining
hypothesis on the **cutoff** equation matches. We do not need an
intertwining condition on the weak lifts used in the pair comparison for
this argument. Symmetry on the limiting null space uses RBase. An
equivariant projection onto that null space lets us inject the nearby
finite-cutoff equation coordinates into it (regardless of whether the
projections of b were orthogonal). Dimension equality comes from the
finite two-sided comparisons. Then cancel the isomorphic submodules. We
give an elementary simultaneous-complement argument to do the latter
without assuming an isomorphism of quotients. Conjugation here is ordinary
conjugation, NOT the combined Euclidean reflection adjoint.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Rank
open Function Set Filter  Extraction Dash Maxwell
open scoped Topology BigOperators ComplexConjugate
variable {G : Gauge} {L : Register G} {d : ℕ}

structure Stable (L : Register G) {d} (A : Submodule ℂ (L.Ref d)) : Prop where
  real : ∀ x ∈ A, star x ∈ A
  hyp (s : Signed) : ∀ x ∈ A, L.mirrorGroup d s x ∈ A

variable {A B : Submodule ℂ (L.Ref d)}












end YM.Push.FiniteDetection.Rank
