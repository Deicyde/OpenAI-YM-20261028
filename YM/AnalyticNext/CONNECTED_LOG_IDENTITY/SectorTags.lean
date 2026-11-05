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
import YM.Pressure.Rows
import YM.Work.D03


set_option warningAsError false

/-!
# One spelling world per actual Forest: pay the shared tag arrays once

Transfer at a fixed S (later even Directed). These identities are *not*
conditional on one word's tags meeting a Plot. Rearrange the whole
finite counting sum, likelihood incl denominators stays in integrand.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Tags
open Lattice Wilson RG Tree Pressure MeasureTheory Function Finset Patch 
open scoped Topology Classical BigOperators ENNReal
variable {G : Gauge} {ι : Type*} {c f : Side} (S : StepData c f)

-- new instance SCOPED to Tags files (lattice Perm order needed for tag measurable)
scoped instance onOrder : MeasurableSpace Lattice.Order := ⊤
scoped instance order_singleton : MeasurableSingletonClass Lattice.Order := ⟨fun _ => trivial⟩

section uniform
variable (α : Type*) [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def lottery : Measure α := (Fintype.card α : ENNReal)⁻¹ • Measure.count



scoped instance ticketOne [Nonempty α] : IsProbabilityMeasure (lottery α) := ⟨by
  rw [lottery,Measure.smul_apply,Measure.count_apply_finite _ Set.finite_univ]
  simp only [Set.Finite.toFinset_eq_toFinset,Set.toFinset_univ,Finset.card_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp only [Nat.cast_ne_zero]; exact Fintype.card_ne_zero) (by simp)⟩

variable [Fintype ι] [DecidableEq ι]


end uniform

section world
variable (G)

abbrev TID := Site c ⊕ Bond c -- fix S arg
abbrev Key (F : Forest S.ratio) := F.Free ⊕ @TID c

def Thing : @TID c → Type
  | .inl _ => S.patch.FrameTag
  | .inr _ => S.patch.Points

def Piece (F : Forest S.ratio) : Key S F → Type
  | .inl _ => G.El
  | .inr i => Thing S i

scoped instance tMeas : ∀ i, MeasurableSpace (Thing S i)
  | .inl _ => (inferInstance : MeasurableSpace S.patch.FrameTag)
  | .inr _ => (inferInstance : MeasurableSpace S.patch.Points)
scoped instance pMeas (F : Forest S.ratio) : ∀ i, MeasurableSpace (Piece G S F i)
  | .inl _ => (inferInstance : MeasurableSpace G.El)
  | .inr i => tMeas S i
scoped instance piece_nonempty (F : Forest S.ratio) : ∀ i, Nonempty (Piece G S F i)
  | .inl _ => (inferInstance : Nonempty G.El)
  | .inr (.inl _) => (inferInstance : Nonempty S.patch.FrameTag)
  | .inr (.inr _) => (inferInstance : Nonempty S.patch.Points)

def tagM : ∀ i, Measure (Thing S i)
  | .inl _ => lottery S.patch.FrameTag
  | .inr _ => lottery S.patch.Points

def draw (F : Forest S.ratio) : ∀ i, Measure (Piece G S F i)
  | .inl _ => G.probHaar
  | .inr i => tagM S i

scoped instance t_probability : ∀ i, IsProbabilityMeasure (tagM S i)
  | .inl _ => ticketOne S.patch.FrameTag
  | .inr _ => ticketOne S.patch.Points

scoped instance p_probability (F : Forest S.ratio) : ∀ i, IsProbabilityMeasure (draw G S F i)
  | .inl _ => (inferInstance : IsProbabilityMeasure G.probHaar)
  | .inr i => t_probability S i

abbrev World (F : Forest S.ratio) := ∀ i, Piece G S F i

def sample (F : Forest S.ratio) : World G S F ≃ᵐ F.Slice G × S.Choices :=
  (MeasurableEquiv.sumPiEquivProdPi _).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (F.Slice G)) (MeasurableEquiv.sumPiEquivProdPi (Thing S)))





def priors : Measure S.Choices := (Measure.pi fun _ => lottery S.patch.FrameTag).prod
  (Measure.pi fun _ => lottery S.patch.Points)

scoped instance : IsProbabilityMeasure (priors S) := by unfold priors; infer_instance






end world
end YM.Push.LogIdentity.Tags
