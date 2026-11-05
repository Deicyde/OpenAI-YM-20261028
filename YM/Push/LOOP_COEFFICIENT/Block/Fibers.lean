import YM.Push.LOOP_COEFFICIENT.Block.Young

/-!
# H²–H¹ counting inequalities on a conservation surface
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Set Finset Matrix Metric Lattice Laurent RG Bloch Wilson Real
open scoped Topology BigOperators Matrix.Norms.L2Operator
variable {D : Type} [Fintype D] [DecidableEq D] [AddCommGroup D]
lemma sum_allowed_three (F : (Fin 3 → D) → ℝ) : ∑ a∈allowed (Fin 3) D,F a = ∑ i, ∑ j : D,F ![-(i+j),i,j] := by
  rw [sum_allowed,← Equiv.sum_comp (finTwoArrowEquiv D).symm,Fintype.sum_prod_type]; apply sum_congr rfl fun i _ => sum_congr rfl fun j _ => congr_arg F ?_
  ext1 l; fin_cases l <;> simp [finTwoArrowEquiv,Fin.sum_univ_two]
lemma sum_allowed_four (F : (Fin 4 → D) → ℝ) : ∑ a∈allowed (Fin 4) D,F a = ∑ i, ∑ j, ∑ k : D,F ![-(i+j+k),i,j,k] := by
  rw [sum_allowed,← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 3 => D)), Fintype.sum_prod_type]; refine sum_congr rfl fun i _ => ?_; rw [← Equiv.sum_comp (finTwoArrowEquiv D).symm, Fintype.sum_prod_type]; apply sum_congr rfl fun j _ => sum_congr rfl fun k _ => congr_arg F ?_
  ext1 l; fin_cases l <;> simp [Fin.consEquiv,finTwoArrowEquiv,Fin.sum_univ_three]

lemma young₃ (f g h : D → ℝ) {p q r A : ℝ} (hA : 1≤A) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (he : p⁻¹+q⁻¹+r⁻¹=2) (hf : ∀ i, 0≤f i) (hg : ∀ i,0≤g i) (hh : ∀ i,0≤h i) (hu : ∑ i,(f i)^p ≤ A) (hv : ∑ i,(g i)^q ≤ A) (hw : ∑ i,(h i)^r ≤ A) :
    ∑ i,∑ j,f (-(i+j)) * g i * h j ≤ A^3 := by
  have hx (r : ℝ) (hr : 1 ≤ r) := inv_le_one_of_one_le₀ hr
  have H := young (f:= ![f,g,h]) (p:= ![p,q,r]) (w:= ![1-p⁻¹,1-q⁻¹,1-r⁻¹]) ?_ ?_ ?_ ?_ hA ?_
  · simpa only [sum_allowed_three, Fin.prod_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_fin_one,Fintype.card_fin] using! H
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> simp <;> first | linarith [hx _ hp] | linarith [hx _ hq] | linarith [hx _ hr]
  · rw [Fin.sum_univ_three]; change (1-_) + (1-_) + (1-_) = _; linarith
  · intro i; fin_cases i <;> rw [Fin.sum_univ_three] <;> simp <;> field_simp at he ⊢ <;> nlinarith
  · intro i; fin_cases i <;> assumption
lemma young₄ (f g h t : D → ℝ) {A : ℝ} (hA : 1≤A) (hf : ∀ i, 0≤f i) (hg : ∀ i,0≤g i) (hh : ∀ i,0≤h i) (ht : ∀ i,0≤t i)
    (hu : ∑ i,(f i)^(3/2:ℝ) ≤ A) (hv : ∑ i,(g i)^(6/5:ℝ) ≤ A) (hw : ∑ i,(h i)^(6/5:ℝ) ≤ A) (hx : ∑ i,(t i)^(3/2:ℝ) ≤ A) :
    ∑ i,∑ j, ∑ l,f (-(i+j+l))*g i*h j*t l ≤ A^4 := by
  have H := young (f:= ![f,g,h,t]) (p:= ![3/2,6/5,6/5,3/2]) (w:= ![1/3,1/6,1/6,1/3]) ?_ ?_ ?_ ?_ hA ?_
  · simpa only [sum_allowed_four, Fin.prod_univ_four, Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_fin_one,Fintype.card_fin] using! H
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> norm_num
  · rw [Fin.sum_univ_four]; norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  · intro i; fin_cases i <;> rw [Fin.sum_univ_four] <;> norm_num [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail, Fin.ext_iff]
  · intro i; fin_cases i <;> assumption

variable {x f : D → ℝ} {A B : ℝ} (hx : ∀ i,0≤x i) (hf : ∀ i,0≤f i) (ha : ∑ i,(x i)^6 ≤ A) (hb : ∑ i,(f i)^2 ≤ B)
include hx hf ha hb
omit [DecidableEq D] [AddCommGroup D] hx hf in
lemma budget_nonneg : 0 ≤ A ∧ 0 ≤ B := ⟨(sum_nonneg fun _ _ => by positivity).trans ha, (sum_nonneg fun _ _ => by positivity).trans hb⟩
omit [DecidableEq D] [AddCommGroup D] in
lemma mix_one : ∑ i,(x i*f i)^(3/2:ℝ) ≤ A+B := by
  have h := mixed_power hx hf (by norm_num : (0:ℝ)≤1/4) (by norm_num : (0:ℝ)≤3/4) (by norm_num) (u:=6) (by simpa using! ha) hb
  obtain ⟨hA,hB⟩ := budget_nonneg ha hb
  simpa only [Real.mul_rpow (hx _) (hf _),show (6*(1/4):ℝ)=3/2 by norm_num,show (2*(3/4):ℝ)=3/2 by norm_num] using h.trans (b:=(1/4)*A+(3/4)*B) (c:=A+B) (by linarith)
omit [DecidableEq D] [AddCommGroup D] in
lemma mix_two : ∑ i,(x i^2*f i)^(6/5:ℝ) ≤ A+B := by
  have h := mixed_power hx hf (by norm_num : (0:ℝ)≤2/5) (by norm_num : (0:ℝ)≤3/5) (by norm_num) (u:=6) (by simpa using! ha) hb
  obtain ⟨hA,hB⟩ := budget_nonneg ha hb
  have he (i) : (x i^(2:ℕ)*f i)^(6/5:ℝ) = (x i^(2:ℕ))^(6/5:ℝ)*(f i)^(6/5:ℝ) := Real.mul_rpow (sq_nonneg _) (hf i)
  simp_rw [he]
  rw [show (6*(2/5):ℝ)=2*(6/5) by norm_num,show (2*(3/5):ℝ)=6/5 by norm_num] at h
  simpa only [Real.rpow_mul (hx _),Real.rpow_two] using h.trans (b:=(2/5)*A+(3/5)*B) (c:=A+B) (by linarith)
end YM.Push.Loops.Block
