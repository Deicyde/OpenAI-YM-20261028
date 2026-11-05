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
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07

set_option warningAsError false

/-!
# Wick books through order l, separate polynomial degrees

Using finite bounded subsets makes the support checks on historical
labels transparent. All on the actual cumulant labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick  Labels MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {j k n : ℕ}

def letterCount : Slot G → ℕ := fun _ => 1
def Length (p : WickPol G) (j : ℕ) := IsWeightedHomogeneous letterCount p j

def above (G : Gauge) (j : ℕ) : Slot G→ℕ := fun i => if i.1≤j then 0 else 1
def pages (G : Gauge) (j : ℕ) := MvPolynomial.weightedHomogeneousSubmodule ℂ (above G j) 0

theorem inBook (p : WickPol G) (j : ℕ) : p∈pages G j ↔ ∀ v ∈ p.vars, v.fst ≤ j := by
  classical
  change IsWeightedHomogeneous _ p 0 ↔ _
  have he (w : Slot G →₀ ℕ) : Finsupp.weight (above G j) w = 0 ↔ ∀ i ∈ w.support,i.fst≤j := by
    rw [Finsupp.weight_apply]; unfold Finsupp.sum
    rw [Finset.sum_eq_zero_iff_of_nonneg (by simp)]
    apply forall_congr'; intro i; apply forall_congr'; intro h
    simp [above, Finsupp.mem_support_iff.mp h]
  constructor
  · intro h v hv
    obtain ⟨i,hi,hh⟩ := (MvPolynomial.mem_vars_iff_mem_support v).mp hv
    exact (he i).mp (h (MvPolynomial.mem_support_iff.mp hi)) v hh
  intro h w hw
  exact (he w).mpr fun i hi => h i ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨w,MvPolynomial.mem_support_iff.mpr hw,hi⟩)










section graded
variable {M : Type*} [AddCommMonoid M]
















end graded
end YM.Extra.FD
