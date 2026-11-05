import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.Laurent.Eval


/-! # Strip to torus to cochain
Coefficient readout without frequency rounding. -/

set_option autoImplicit false
noncomputable section
namespace YM.Laurent
open Lattice Matrix Finset Filter
open RG MeasureTheory Set Function Topology Complex UnitAddTorus
open scoped Topology BigOperators ContDiff ComplexConjugate ENNReal

variable {α : Type*} [Fintype α]

/-- require periods only inside analytic strip. -/
structure Vane (u : Phase α → ℂ) (η : ℝ) : Prop where
  side : 0<η
  hol (p) : p∈strip η → DifferentiableAt ℂ u p
  reset (p) : p∈strip η → ∀ x, u (p+reciprocal x)=u p

abbrev Rim (α : Type*) := UnitAddTorus α
abbrev Corn (α : Type*) := α → ℝ

variable (α)
def dress (x : Corn α) : Rim α := fun i => (x i : UnitAddCircle)
def walk (x : Corn α) : Phase α := fun i => 2*(Real.pi:ℂ)*x i
omit [Fintype α] in
theorem fashion : Surjective (dress α) := by
  intro x
  choose f hf using fun i => QuotientAddGroup.mk_surjective (x i)
  exact ⟨f,funext hf⟩
omit [Fintype α] in
theorem dressed : IsQuotientMap (dress α) := by
  refine IsOpenMap.isQuotientMap ?_ ?_ (fashion α)
  · exact IsOpenMap.piMap (f:=fun _ : α => (QuotientAddGroup.mk : ℝ → UnitAddCircle))
      (fun _ => QuotientAddGroup.isOpenMap_coe) (Eventually.of_forall (fun _ => QuotientAddGroup.mk_surjective))
  exact continuous_pi fun i => QuotientAddGroup.continuous_mk.comp (continuous_apply i)

variable {α}
def veils (u : Phase α → ℂ) (p : Phase α) : Rim α → ℂ := fun z => u (p+walk α ((fashion α z).choose))

omit [Fintype α] in
theorem stays (x : Corn α) {η : ℝ} {p : Phase α} (h : p∈ strip η) : p+walk α x∈strip η := by
  intro i; simpa [walk] using h i

variable {u : Phase α → ℂ} {η : ℝ}
omit [Fintype α] in
theorem Vane.steps (h : Vane u η) {p} (hp : p∈strip η) (x : Corn α) : veils u p (dress α x)=u (p+walk α x) := by
  let y := (fashion α (dress α x)).choose
  have hb (i : α) : ∃ k : ℤ, x i=y i+k := by
    have he : dress α x=dress α y := (fashion α (dress α x)).choose_spec.symm
    obtain ⟨k,hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp
      (show (x i : UnitAddCircle)= (y i : UnitAddCircle) from congr_fun he i))
    simp only [zsmul_eq_mul,mul_one] at hk; exact ⟨k,by linarith⟩
  choose k hk using hb
  rw [show p+walk α x=p+walk α y+reciprocal k by
    ext1 i; simp only [walk,Pi.add_apply,hk, Complex.ofReal_add,mul_add,reciprocal]; push_cast; abel,
    h.reset _ (stays y hp)]
  rfl

def Vane.guise (h : Vane u η) {p : Phase α} (hp : p∈ strip η) : C(Rim α,ℂ) where
  toFun := veils u p
  continuous_toFun := by
    rw [(dressed α).continuous_iff]
    simp_rw [Function.comp_def,h.steps hp]
    rw [continuous_iff_continuousAt]
    intro x
    refine (h.hol _ (stays x hp)).continuousAt.comp (f:=fun x => p+walk α x) ?_
    apply Continuous.continuousAt
    unfold walk; fun_prop

theorem wears (s : Shift α) (x : Corn α) : mFourier s (dress α x)=mode (walk α x) s := by
  simp only [mFourier, ContinuousMap.coe_mk,dress,fourier_coe_apply,mode,mul_sum,Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1; simp only [walk,Complex.ofReal_one,div_one]; ring

/-- actual symbol coefficients -/
def market (u : Phase α → ℂ) (p : Phase α) (x : Shift α) : ℂ := mFourierCoeff (veils u p) x

-- The three local UnitAddCircle instances adapt Mathlib.Analysis.Fourier.AddCircleMulti (formatting changes). Copyright (c) 2023 David Loeffler. All rights reserved. Apache-2.0. See NOTICE.
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def globe (α : Type*) [Fintype α] : Measure (Rim α) := volume
instance : IsProbabilityMeasure (globe α) := inferInstanceAs (IsProbabilityMeasure volume)
instance : (globe α).IsAddRightInvariant := inferInstanceAs ((volume : Measure (Rim α)).IsAddRightInvariant)

theorem market_cap (h : Vane u η) {p : Phase α} (hp : p∈strip η) (x : Shift α) (K : ℝ) (he : ∀ q∈ strip η,‖u q‖ ≤ K) : ‖market u p x‖ ≤ K := by
  let f := fun a : Rim α => mFourier (-x) a • veils u p a
  have ht (a : Rim α) : ‖f a‖ ≤ K := by
    obtain ⟨a,rfl⟩ := fashion α a
    dsimp only [f]; rw [h.steps hp, norm_smul]
    apply le_trans (mul_le_mul_of_nonneg_right ((mFourier (-x)).norm_coe_le_norm _) (norm_nonneg _))
    rw [mFourier_norm,one_mul]; exact he _ (stays _ hp)
  change ‖∫ a,f a ∂globe α‖ ≤ _
  apply (norm_integral_le_of_norm_le_const (Eventually.of_forall ht)).trans; simp

/-- multiply mode from p into contour -/
def lens (u : Phase α → ℂ) (x : Shift α) : Phase α → ℂ := fun p => mode p (-x)*u p

lemma Vane.lens (h : Vane u η) (x : Shift α) : Vane (lens u x) η :=
  ⟨h.side, fun p hp => (show DifferentiableAt ℂ (fun p => mode p (-x)) p by unfold mode; fun_prop).mul (h.hol p hp),
   fun a ha i => by simp only [Laurent.lens,mode_phase,h.reset a ha,mode_periodic,mul_one]⟩

lemma adoption (h : Vane u η) {p} (hp : p∈ strip η) (x : Shift α) :
    (∫ a, veils (lens u x) p a ∂globe α)=mode p (-x)*market u p x := by
  change _ = _ * ∫ a, _ ∂globe α
  rw [← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  obtain ⟨a,rfl⟩ := fashion α a
  dsimp only
  rw [(h.lens x).steps hp,h.steps hp,lens,mode_phase,wears,smul_eq_mul,mul_assoc]
end YM.Laurent
