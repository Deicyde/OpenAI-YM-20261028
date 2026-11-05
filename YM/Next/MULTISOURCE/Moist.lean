import YM.Next.MULTISOURCE.Curves
import YM.Next.MULTISOURCE.Germs
import YM.Next.MULTISOURCE.Grades


/-! pointwise test conversion on coefficient H/K slots -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open RG Wilson Lattice Finset Filter MeasureTheory Marker MvPolynomial
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {n : Side} {G : Gauge}

def taps (P : BudgetPoint) (Y : Support n) (F : Config G n → ℂ) : Set ℝ := {t | 0 ≤ t ∧ ∀ x∈Y,P.supBounds x Y F t}
lemma tap_le {P : BudgetPoint} {Y : Support n} {F : Config G n → ℂ} {t : ℝ} (h : t∈taps P Y F) :
    sInf (taps P Y F) ≤ t := csInf_le ⟨0,fun _ h => h.1⟩ h
lemma has_tap {P : BudgetPoint} {Y : Support n} {F : Config G n → ℂ} (h : (taps P Y F).Nonempty) :
    sInf (taps P Y F) ∈ taps P Y F := by
  have he : 0 ≤ sInf (taps P Y F) := le_csInf h fun _ ht => ht.1
  refine ⟨he,fun x hx => ⟨he,fun U hU l hl hh => le_csInf h (fun i hi => ?_)⟩⟩
  exact (hi.2 x hx).2 U hU l hl hh

def boxp (F : Config G n → ℂ) : Set ℝ := {t | 0 ≤ t ∧ ∀ U, ‖F U‖≤t}
lemma box_le {F : Config G n → ℂ} {t : ℝ} (he : t∈boxp F) : sInf (boxp F) ≤ t := csInf_le ⟨0,fun _ h => h.1⟩ he
lemma has_box {F : Config G n → ℂ} (h : (boxp F).Nonempty) : sInf (boxp F) ∈ boxp F :=
  ⟨le_csInf h (fun _ ha => ha.1),fun U => le_csInf h fun _ ht => ht.2 U⟩

section
variable {P : BudgetPoint} {Y : Support n} {F : Config G n → ℂ}

lemma shapes (z : ℂ) {B : ℝ} (h : B∈ taps P Y F) : ‖z‖*B∈ taps P Y (z • F) := by
  have he : 0 ≤ ‖z‖*B := mul_nonneg (norm_nonneg _) h.1
  refine ⟨he,fun i hi => ⟨he,fun U hu l hl ha => ?_⟩⟩
  rw [scaled_left,norm_mul]; exact mul_le_mul_of_nonneg_left ((h.2 i hi).2 U hu l hl ha) (norm_nonneg _)
lemma cubes (z : ℂ) {B : ℝ} (h : B∈boxp F) : ‖z‖*B∈boxp (z • F) := ⟨mul_nonneg (norm_nonneg _) h.1,fun U =>
    (norm_smul z (F U)).trans_le (mul_le_mul_of_nonneg_left (h.2 U) (norm_nonneg _))⟩
lemma sum_taps {I : Type*} (S : Finset I) (f : I → Config G n → ℂ) (k : I → ℝ)
    (h : ∀ i,P.Regular Y (f i) ∧ k i∈taps P Y (f i)) :
    P.Regular Y (∑ i∈S,f i) ∧ (∑ i∈S,k i) ∈ taps P Y (∑ i∈S,f i) := by
  induction S using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact ⟨(null_path ..).1,le_rfl,fun i _ => (null_path P Y).2 i⟩
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    obtain ⟨he,hp,hk⟩ := ih
    exact ⟨Puff.combine (h i).1 he, add_nonneg (h i).2.1 hp,
      fun j hj => Puff.balances (h i).1 he _ ((h i).2.2 j hj) (hk j hj)⟩
lemma sum_box {Y : Pack n} {I : Type*} (S : Finset I) (f : I → Config G n → ℂ) (k : I → ℝ)
    (h : ∀ i, Legible P Y (f i) ∧ k i∈boxp (f i)) :
    Legible P Y (∑ i∈S,f i) ∧ (∑ i∈S,k i) ∈ boxp (∑ i∈S,f i) := by
  induction S using Finset.induction with
  | empty => simp only [sum_empty]; exact ⟨Legible.zero ..,le_rfl,fun i => norm_zero.le⟩
  | insert i S hi ih =>
    simp only [sum_insert hi]
    exact ⟨(h i).1.add ih.1,add_nonneg (h i).2.1 ih.2.1,fun U => (norm_add_le ..).trans
      (add_le_add ((h i).2.2 U) (ih.2.2 U))⟩
end

variable {I : Type*} [DecidableEq I] [Fintype I]

lemma tariffH (P : BudgetPoint) (F : Config G n → Wave I) (Y : Support n) (q : Grade I) {N : ℕ} (r : I→ℝ)
    (he : ∀ i, q i < N) (hr : 0 < price r q) (hp : 0<N)
    (hh : ∀ x (p : Grade I), p∈(F x).support → ∀ i,p i < N)
    (f : Cir I N → ℝ) (H : ∀ i, P.Regular Y (eval (looped r N i) ∘ F) ∧ f i∈taps P Y (eval (looped r N i) ∘ F)) :
    P.Regular Y (fun U => coeff q (F U)) ∧ (∑ i, ‖load r N i q‖*f i) ∈ taps P Y (fun U => coeff q (F U)) := by
  let g (i : Cir I N) : Config G n → ℂ := load r N i q • (eval (looped r N i) ∘ F)
  rw [show (fun U => coeff q (F U))=∑ i,g i from funext fun i => by
    rw [Finset.sum_apply]; exact display r q (F i) hp hr he (fun p => hh i p)]
  exact sum_taps _ g _ fun i => ⟨path_scaled _ (H i).1, shapes _ (H i).2⟩
lemma tariffK (P : BudgetPoint) (F : Config G n → Wave I) (Y : Pack n) (q : Grade I) {N : ℕ} (r : I→ℝ)
    (he : ∀ i, q i < N) (hr : 0 < price r q) (hp : 0<N)
    (hh : ∀ x (p : Grade I), p∈(F x).support → ∀ i,p i < N)
    (f : Cir I N → ℝ) (H : ∀ i, Legible P Y (eval (looped r N i) ∘ F) ∧ f i∈boxp (eval (looped r N i) ∘ F)) :
    Legible P Y (fun U => coeff q (F U)) ∧ (∑ i, ‖load r N i q‖*f i) ∈ boxp (fun U => coeff q (F U)) := by
  let g (i : Cir I N) : Config G n → ℂ := load r N i q • (eval (looped r N i) ∘ F)
  rw [show (fun U => coeff q (F U))=∑ i,g i from funext fun i => by
    rw [Finset.sum_apply]; exact display r q (F i) hp hr he (fun p => hh i p)]
  exact sum_box _ g _ fun i => ⟨(H i).1.scale _, cubes _ (H i).2⟩
end YM.Multi.Desk
