import YM.Analysis.Nonnegative
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Shared Gram completion and bounded operators

Roughly the analysis skeleton requested in both extraction and reconstruction.
Linear-in-second. Not a spectral theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM
open Function Set Filter UniformSpace
open Analysis
open scoped Topology BigOperators InnerProductSpace ComplexOrder ComplexConjugate

structure Hilbert where
  space : Type
  [normed : NormedAddCommGroup space]
  [ips : InnerProductSpace ℂ space]
  [complete : CompleteSpace space]

namespace Hilbert
attribute [instance] Hilbert.normed Hilbert.ips Hilbert.complete
instance : CoeSort Hilbert Type := ⟨fun H => H.space⟩
abbrev Op (H : Hilbert) := H →L[ℂ] H
end Hilbert

namespace Kernel
variable {X : Type} {K : X → X → ℂ}

structure Gram (K : X → X → ℂ) where
  H : Hilbert
  plant : X → H
  dense : Dense ((Submodule.span ℂ (Set.range plant) : Set H))
  measure x y : inner ℂ (plant x) (plant y) = K x y

private abbrev raw (X : Type) := X →₀ ℂ

@[implicit_reducible]
def core (H : NNKernel K) : PreInnerProductSpace.Core ℂ (raw X) where
  inner f g := f.sum fun x p => g.sum fun y q => star p*q*K x y
  conj_inner_symm f g := by
    rw [Finsupp.sum_comm]; simp only [map_finsuppSum,map_mul,← Complex.star_def,star_star,H.swaps]
    congr! 6; ring
  add_left f g h := by rw [Finsupp.sum_add_index'] <;> simp [add_mul,Finsupp.sum_add]
  smul_left := by
    intro x y c; rw [Finsupp.sum_smul_index] <;> simp [Finsupp.mul_sum,mul_left_comm,mul_comm]
  re_inner_nonneg := by
    intro f
    have he := H.positivity (I := ↥f.support) (fun x => x.val) (fun x => f x.val)
    change 0 ≤ ∑ x ∈ f.support.attach, ∑ y ∈ f.support.attach, star _ * _ * _ at he
    simp only [mul_right_comm _ (K _ _) _] at he
    have hh : ∑ x ∈ f.support.attach, ∑ y ∈ f.support.attach, star (f x)*f y*K x y =
        ∑ x ∈ f.support, ∑ y ∈ f.support, star (f x)*f y*K x y := by
      have he (x : ↥f.support) : (∑ y ∈ f.support.attach, star (f x)*f y*K x y) = _ :=
        Finset.sum_attach f.support fun y => star (f x)*f y*K x y
      simp_rw [he]
      exact Finset.sum_attach f.support (fun x => ∑ y ∈ f.support, star (f x)*f y*K x y)
    rw [hh] at he; exact he.1

/-- Kolmogorov data for any actual port kernel. Use Mathlib completion of
*semi*normed groups to obtain the separated Hilbert space, don't declare
an inner norm instance on Finsupp globally. -/
theorem host (H : NNKernel K) : Nonempty (Gram K) := by
  classical
  letI := core H
  letI q : SeminormedAddCommGroup (raw X) := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ (raw X) := InnerProductSpace.ofCore (core H)
  let D : Hilbert := { space := Completion (raw X) }
  let S (x : X) : D := (Finsupp.single x (1:ℂ) : raw X)
  refine ⟨D,S,?_,?_⟩ -- dest constructor Nonempty?
  · let C : Submodule ℂ D := Submodule.span ℂ (Set.range S)
    have he (f : raw X) : (Completion.coe' f : D) ∈ C := by
      induction f using Finsupp.induction_linear with
      | zero => rw [show Completion.coe' (0 : raw X) = 0 from Completion.coe_zero]; exact C.zero_mem
      | add f g hf hg =>
        have hz : Completion.coe' (f+g) = Completion.coe' f + Completion.coe' g := Completion.coe_add _ _
        rw [hz]; exact C.add_mem hf hg
      | single a f =>
        have ht : Completion.coe' (Finsupp.single a f : raw X) = f • S a := by
          dsimp only [S]
          rw [← Completion.coe_smul]
          congr 1; simp
        rw [ht]; apply C.smul_mem; exact Submodule.subset_span ⟨_,rfl⟩
    refine Dense.mono (s₁ := Set.range (Completion.coe' : raw X → D)) ?_ Completion.denseRange_coe
    rintro a ⟨p,rfl⟩; exact he p
  intro x y; change inner ℂ (_ : Completion (raw X)) _ = _; unfold S; rw [Completion.inner_coe]
  change ((Finsupp.single x (1:ℂ)).sum _) = _
  simp

namespace Gram
variable (S : Gram K)

def stems : (X →₀ ℂ) →ₗ[ℂ] S.H := Finsupp.linearCombination _ S.plant

lemma whole : DenseRange S.stems := by
  change Dense ((LinearMap.range S.stems : Set S.H))
  rw [stems, Finsupp.range_linearCombination]
  exact S.dense

@[simp] theorem one (x) : S.stems (Finsupp.single x 1) = S.plant x := by simp [stems]

lemma by_bud {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] {V W : S.H →L[ℂ] M}
    (h : ∀ x, V (S.plant x) = W (S.plant x)) : V=W := by
  have ht (x : X →₀ ℂ) : V (S.stems x)=W (S.stems x) := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add,hf,hg]
    | single a r => simp [stems,h]
  exact DFunLike.coe_injective (S.whole.equalizer V.continuous W.continuous (funext ht))

/-- Implement the operators that are bounded on all word sums, using
dense range. Null is automatically respected by this bound. -/
lemma by_bound {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [CompleteSpace M]
    (p : X → M) (C : ℝ) (hc : 0 ≤ C) (H : ∀ f : X →₀ ℂ,
      ‖Finsupp.linearCombination ℂ p f‖ ≤ C * ‖S.stems f‖) :
    ∃ U : S.H →L[ℂ] M, ‖U‖ ≤ C ∧ ∀ i, U (S.plant i) = p i := by
  let L := Finsupp.linearCombination ℂ p
  let U := L.extendOfNorm S.stems
  refine ⟨U, LinearMap.opNorm_extendOfNorm_le S.whole hc H,fun i => ?_⟩
  rw [← S.one]
  rw [show U _ = Finsupp.linearCombination _ _ _ from LinearMap.extendOfNorm_eq S.whole ⟨C,H⟩ _]
  simp
end Gram
end Kernel
end YM
