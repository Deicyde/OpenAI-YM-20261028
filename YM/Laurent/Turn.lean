import Mathlib.Analysis.Complex.CauchyIntegral
import YM.Laurent.Rune

/-! # Periodic analytic sweeping in real and imaginary moves -/
set_option autoImplicit false
noncomputable section
namespace YM.Laurent
open Lattice Matrix Finset Filter RG MeasureTheory Set Function Topology Complex UnitAddTorus
open scoped Topology BigOperators ContDiff ComplexConjugate ENNReal Interval

variable {α : Type*} [Fintype α]
section bump
variable [DecidableEq α]
private def turn (i : α) (x : ℝ) := dress α (Pi.single i x)
private lemma shifting (i : α) (f : Rim α → ℂ) (h : Continuous f) :
    (∫ x, f x ∂globe α)=∫ x, (∫ y : ℝ in 0..1,f (x+turn i y)) ∂globe α := by
  let μ := (volume:Measure ℝ).restrict (Set.Ioc 0 1)
  let F := fun z : ℝ × Rim α => f (z.2+turn i z.1)
  have he : Continuous F := by
    refine h.comp (continuous_snd.add (Continuous.comp (g:=turn i) ?_ continuous_fst))
    unfold turn; apply Continuous.comp (dressed α).continuous
    apply continuous_pi; intro j; by_cases hh : j=i
    · simp only [hh,Pi.single_eq_same]; fun_prop
    simp only [Pi.single_eq_of_ne hh]; fun_prop
  haveI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hh : Integrable F (μ.prod (globe α)) := by
    obtain ⟨b,hb⟩ := ((isCompact_range h).image continuous_norm).bddAbove
    apply Integrable.of_bound he.aestronglyMeasurable b
    exact Eventually.of_forall fun z => hb ⟨F z, ⟨_,rfl⟩,rfl⟩
  have hb (x : ℝ) : (∫ y,F (x,y) ∂globe α)=∫ y,f y ∂globe α :=
    (measurePreserving_add_right (globe α) _).integral_comp (Homeomorph.addRight (turn i x)).measurableEmbedding _
  rw [show (∫ x, f x ∂globe α)=∫ z,F z∂μ.prod (globe α) by rw [integral_prod F hh]; simp_rw [hb]; simp]
  rw [integral_prod_symm F hh]; simp only [intervalIntegral.integral_of_le zero_le_one]; rfl

private lemma woven {u : Phase α → ℂ} {η : ℝ} (h : Vane u η) {p q : Phase α} (hp : p∈ strip η) (hq : q∈strip η)
    (i : α) (hh : ∀ j, j≠i → q j=p j) :
    (∫ x, veils u p x∂globe α)=∫ x, veils u q x∂globe α := by
  rw [shifting i (veils u p) (h.guise hp).continuous,shifting i (veils u q) (h.guise hq).continuous]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  obtain ⟨a,rfl⟩ := fashion α a
  let P := p+walk α a
  let Q := q+walk α a
  let e := 2*Real.pi
  have he : 0<e := by unfold e; positivity
  let r := P i/e; let s := Q i/e
  have hr : P i=(e:ℂ)*r := by unfold r; field_simp [he.ne']
  have hs : Q i=(e:ℂ)*s := by unfold s; field_simp [he.ne']
  let w := fun z : ℂ => update P i ((e:ℂ)*z)
  let F := u ∘ w
  have ha (p : Phase α) (hp : p∈strip η) (z : Corn α) (t : ℝ) (x : Rim α) (hh : dress α z=x) : veils u p (x+turn i t) = u (p+walk α (z+Pi.single i t)) := by
    subst x
    rw [show dress α z+turn i t=dress α (z+Pi.single i t) by
      ext1 j; exact (map_add (QuotientAddGroup.mk' _) (z j) ((Pi.single i t: Corn α) j)).symm,h.steps hp]
  have hF (p : Phase α) (hp : p∈strip η) (z : ℂ) (heq : (p+walk α a) i=(e:ℂ)*z)
      (hw : ∀ j,j≠i → (p+walk α a) j=P j) : (∫ t : ℝ in 0..1,veils u p (dress α a+turn i t)) =
      ∫ t : ℝ in z.re..z.re+1, F (t+(z.im:ℂ)*Complex.I) := by
    have hh := intervalIntegral.integral_comp_add_right (a:=0) (b:=1) (fun t : ℝ => F (t+(z.im:ℂ)*Complex.I)) z.re
    rw [zero_add,add_comm 1] at hh; rw [← hh]
    apply intervalIntegral.integral_congr; intro x _; dsimp only; rw [ha p hp a x _ rfl, Complex.ofReal_add,add_assoc, Complex.re_add_im]
    unfold F Function.comp; congr 1; ext1 j; by_cases h : j=i
    · subst j; unfold w; rw [update_self]; simp only [Pi.add_apply,walk,Pi.single_eq_same, Complex.ofReal_add, mul_add]
      simp only [Pi.add_apply,walk] at heq; unfold e at *; rw [← heq]; push_cast; abel
    unfold w; simp only [update_of_ne h]; rw [← hw j h]; simp only [walk, Pi.add_apply, Pi.single_eq_of_ne h, add_zero]
  have hy : ∀ j,j≠i → Q j=P j := fun j hj => by simp [Q,P,hh j hj]
  dsimp only
  rw [hF p hp r hr (by intros; rfl),hF q hq s hs hy]
  have ht (z : ℂ) (hz : z.im∈ [[r.im,s.im]]) : w z ∈ strip η := by
    intro j; by_cases hj : j=i
    · subst j
      have hx := stays a hp i; have hq := stays a hq i; change |(P i).im|<η at hx; change |(Q i).im|<η at hq
      rw [hr] at hx; rw [hs] at hq
      unfold w; rw [update_self]
      simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul,add_zero,abs_lt] at hx hq ⊢
      rw [Set.mem_uIcc] at hz; rcases hz with h|h <;> constructor <;> nlinarith only [he,hx,hq,h]
    unfold w; rw [update_of_ne hj]; exact stays a hp j
  have HK (x : ℂ) (hx : x.im∈ [[r.im,s.im]]) : F (x+1)=F x := by
    unfold F Function.comp
    rw [show w (x+1)= w x + reciprocal (Pi.single i 1) by
      ext1 j; by_cases h : j=i
      · simp only [h,w, update_self,Pi.add_apply,mul_add,mul_one,reciprocal,Pi.single_eq_same,Int.cast_one]
        unfold e; push_cast; ring
      simp only [w,update_of_ne h, Pi.add_apply,reciprocal, Pi.single_eq_of_ne h,Int.cast_zero,mul_zero,add_zero] ]
    exact h.reset _ (ht x hx) _
  let z : ℂ := ⟨r.re+1,s.im⟩
  have hw : DifferentiableOn ℂ F ([[r.re,z.re]] ×ℂ [[r.im,z.im]]) := by
    intro x hx; apply DifferentiableAt.differentiableWithinAt
    apply (h.hol _ (ht _ hx.2)).comp (f:=w) _
    rw [differentiableAt_pi]; intro j; by_cases h : j=i
    · simp only [h,w,update_self]; fun_prop
    simp only [w,update_of_ne h]; fun_prop
  have hm := integral_boundary_rect_eq_zero_of_differentiableOn F r z hw
  rw [show (∫ y : ℝ in r.im..z.im,F (↑z.re+(y:ℂ)*Complex.I)) = (∫ y : ℝ in r.im..z.im,F (↑r.re+(y:ℂ)*Complex.I)) by
    refine intervalIntegral.integral_congr fun y h => ?_
    dsimp only [z]; push_cast; rw [add_right_comm]; exact HK _ (by simpa using h)] at hm
  rw [add_sub_cancel_right] at hm; rw [sub_eq_zero] at hm; rw [hm]
  let g := fun t : ℝ => F (t+(s.im:ℂ)*Complex.I)
  have hg : Function.Periodic g 1 := by
    intro t; unfold g; push_cast; rw [add_right_comm]; apply HK
    simp
  exact hg.intervalIntegral_add_eq _ _
end bump

lemma full_turn {u : Phase α → ℂ} {η : ℝ} (h : Vane u η) {p q} (hp : p∈strip η) (hq : q∈strip η) :
    (∫ x,veils u p x∂globe α)=∫ x,veils u q x∂globe α := by
  classical
  let P (s : Finset α) (i : α) := if i∈s then q i else p i
  have ht (s : Finset α) : P s∈strip η := by intro i; dsimp only [P]; split; exact hq i; exact hp i
  have he (s : Finset α) : (∫ x,veils u p x∂globe α)=∫ x,veils u (P s) x∂globe α := by
    induction s using Finset.induction with
    | empty => simp only [P,Finset.notMem_empty,↓reduceIte]
    | insert i s he ih => rw [ih]; exact woven h (ht s) (ht _) i fun j hj => by simp [P,hj]
  simpa only [P,Finset.mem_univ,↓reduceIte] using he univ

lemma coat_price {u : Phase α → ℂ} {η : ℝ} (h : Vane u η) {p} (hp : p∈ strip η) (x : Shift α) :
    market u p x=mode p x*market u 0 x := by
  have he : (0 : Phase α)∈strip η := fun i => by simpa using h.side
  have hh := full_turn (h.lens x) hp he
  rw [adoption h hp,adoption h he, mode_opposite,mode_constant,one_mul] at hh; rw [← hh,mul_inv_cancel_left₀ (mode_ne p x)]
end YM.Laurent
