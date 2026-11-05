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
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Bid.Drops
import YM.Next.MULTISOURCE.Vacancy
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15

set_option warningAsError false

/-! # Small-flag sector, true bill on the unmarked partners

This bound does NOT divide by P.eval and doesn't use crude all-sites.
Per fixed configuration. Even compatible with wraps and repeated roots at
one flag cluster. For higher-rank/arrays need further methods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Alphabet
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Labels Multi Multi.Pack
open Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {n : Side} {G : Gauge} {F : Config G n→ℂ} {X : Support n} {κ : ℝ}

/-- Mint at stock exponent needs no gate (higher exponents do). -/
lemma mint_zero (P : Rep G n) {δ μ : ℝ} (h : P.activities.Valid P.p δ μ) : Mint P 0 μ := by
  apply Multi.mint_from (le_refl 0)
  obtain ⟨f,hf,hQ⟩ := h.boundK
  refine ⟨f,hf,?_⟩
  simp_rw [reserve,BudgetPoint.mass,add_zero]; exact hQ



private lemma paid (P : Rep G n) {X Y : Support n} {u : ℝ} (h : 0 ≤ u) (hQ : X⊆Y) :
    burn P.p u X ≤ burn P.p u Y := Real.exp_monotone (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Corona.cover_mono hQ P.p.B) (add_nonneg P.p.exponent_pos.le h))


end YM.AnalyticNext.GridStop.Alphabet
