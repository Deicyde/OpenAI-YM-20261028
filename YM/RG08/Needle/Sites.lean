import YM.RG08.Needle.Ash
/-!
# Product topology of coefficients: triangular leading, local inverse per sector
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PowerSeries
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {I:Type} [Fintype I] [DecidableEq I] {G:Gauge} {L c f p: Side}{w R A B:ℝ}{D d e r n k t:ℕ}{τ:ℕ}{F:Labels.Frame G d}
variable {T U:Session (Letter F)} {A':Session I}{i j:Letter F} -- shadow j sorting
lemma blazing (h:Flash L T) : LitP (hot T⁻¹ 0) ∧ (∀ i j : Letter F, i≠ j→ hot T⁻¹ 0 i j≠0→ casc j<casc i) ∧ ∀ i:Letter F, hot T⁻¹ 0 i i= ((L.val:ℝ)^(d-fee i))⁻¹ := by
  obtain ⟨he,hv,hh⟩:= shellP_tri (arcades h)
  rw [inclosure h,askIT]
  refine ⟨fun i j hp=> he i j (fun hc=>hp (by rw [diagonal_mul,hc,mul_zero])),fun i j hj hp=> hv _ _ hj (fun hc=>hp (by rw [diagonal_mul,hc,mul_zero])),fun i=>?_⟩
  rw [diagonal_mul,hh,h.dollar,mul_one]
-- Uniform before L
lemma priceHat (h:Flash L T)(i:Letter F): ‖(hot T 0 i i)⁻¹‖ ≤ 1 := by rw [Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans (lamp h i)))]; exact inv_le_one_of_one_le₀ (lamp h i)
lemma lift_ac {X: Loft F} (h:HollowP X)(hp:0≤A)(he:∀ i j,slot i=slot j→ ‖X i j‖ ≤ A) (n : ℕ) (p:slot i=slot j): ‖(X^n) i j‖≤ (Fintype.card (Letter F)*A)^n := by
  induction n generalizing i j with
  | zero=> simp only [pow_zero,Matrix.one_apply]; split_ifs <;> simp
  | succ n ih=>
    rw [pow_succ,Matrix.mul_apply]
    let R:= ((Fintype.card (Letter F):ℝ)*A)^n
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ _ : Letter F,R*A := Finset.sum_le_sum fun k _=>by
        by_cases hx:(X^n) i k*X k j=0; swap
        · obtain ⟨h₁,h₂⟩:=mul_ne_zero_iff.mp hx; have hT:=le_antisymm ((h.1 k j h₂).trans p.ge) (shapeH h _ i k h₁).1
          rw [norm_mul]; exact mul_le_mul (ih hT.symm) (he k j (hT.trans p)) (norm_nonneg _) (by unfold R; positivity)
        rw [hx,norm_zero]; unfold R; positivity
      _ = _ := by unfold R; simp; ring
lemma shell_pays {X: Loft F} (h:HollowP X)(he:∀ i j,slot i=slot j→ ‖X i j‖ ≤ A)(hp:0≤A)(p:slot i=slot j) : ‖shellP X i j‖ ≤ ∑ n∈range (insolent F), (Fintype.card (Letter F)*A)^n := by rw [shellP, Matrix.sum_apply]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> lift_ac h hp he i p)
lemma wingTips (h:Flash L T)(he : ∀ i j, slot i=slot j → ‖hot T 0 i j‖ ≤ A*((L.val:ℝ)^(d-fee j))) (hp:0≤A)(i j)(hv:slot i=slot j): ‖hot T⁻¹ 0 i j‖≤ ∑ n∈range (insolent F), (Fintype.card (Letter F)*(A+1))^n := by
  have hP i j (p: slot i=slot j) : ‖ace (hot T 0) i j‖ ≤ A+1 := by
    unfold ace askIT; rw [Matrix.sub_apply,mul_diagonal,h.dollar]; let Q:=(L.val:ℝ)^(d-fee j); have hQ:0<Q:= by unfold Q; positivity
    apply (norm_sub_le ..).trans
    calc
      _ ≤ 1+A := add_le_add (by rw [Matrix.one_apply]; split <;> simp) (by rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hQ.le)]; exact (mul_le_mul_of_nonneg_right (he i j p) (inv_nonneg.mpr hQ.le)).trans_eq (mul_inv_cancel_right₀ hQ.ne' _) ) -- name
      _=_:=add_comm ..
  rw [inclosure h,askIT, diagonal_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (priceHat h i)).trans (shell_pays (arcades h) hP (by linarith) hv)
def diagonalSl (T: Loft F) : Loft F:=Matrix.of (fun i j=> if slot i=slot j then T i j else 0)
lemma horiz {X Y:Loft F}(hp : LitP X)(hY: LitP Y) : diagonalSl (X*Y)=diagonalSl X*diagonalSl Y := by -- add binders
  ext i j; rw [Matrix.mul_apply]
  unfold diagonalSl; simp only [Matrix.of_apply]; split
  next h=>
    rw [Matrix.mul_apply]; apply sum_congr rfl; intro k _
    split_ifs with he hx hx; rfl
    all_goals first|omega|rw [show X i k*Y k j=0 from not_ne_iff.mp (fun hb=> by obtain ⟨hv,hw⟩:=mul_ne_zero_iff.mp hb; have ht:=hp i k hv; have hh:=hY k j hw; omega)]; ring
  next h=>symm; apply sum_eq_zero; intro k hk; split_ifs <;> first|omega|ring
lemma crown_slot (h:Flash L T): diagonalSl (hot T 0)*diagonalSl (hot T⁻¹ 0)=1 := by rw [← horiz (fun i j he=> by simpa using h.stairs 0 i j he) (blazing h).1,← hot_m0,Matrix.mul_nonsing_inv T (recoupC h), hot_one,if_pos rfl]; ext i j; by_cases he:i=j<;> simp [diagonalSl,Matrix.one_apply, he,ite_self]
lemma invert_coin (h:IsUnit A'.det) (n:ℕ): hot A'⁻¹ (n+1) = -(hot A'⁻¹ 0) * (∑ j∈(wheel (n+1)).filter (fun j=> 0<j.1), hot A' j.1 * hot A'⁻¹ j.2) := by
  let Q i:=(hot A' i); let U i:= hot A'⁻¹ i; let X := ∑ j ∈(wheel (n+1)).filter (fun j=> 0<j.1), Q j.1 * U j.2
  have hp : (∑ i∈wheel (n+1), Q i.1 * U i.2)=0 := by
    rw [show (∑ i∈wheel (n+1),Q i.1 * U i.2)=_ from (hot_mul ..).symm, Matrix.mul_nonsing_inv _ h,hot_one,if_neg (Nat.succ_ne_zero n)]
  have hz : X+Q 0*U (n+1)=0:= by
    rw [← Finset.sum_erase_add _ _ (?_: (0,n+1)∈wheel (n+1))] at hp; swap; · simp [wheel]
    unfold X; rw [show (wheel (n+1)).filter (fun j=>0<j.1)=(wheel (n+1)).erase (0,n+1) from ?_]; exact hp
    ext ⟨i,j⟩; simp [wheel]; omega
  have hv : U 0 * Q 0=1:= by rw [show U 0*Q 0=_ from (hot_m0 ..).symm, Matrix.nonsing_inv_mul _ h,hot_one,if_pos rfl]
  change U _= -(U 0)*X; rw [show X= -(Q _*U _) from eq_neg_of_add_eq_zero_left hz, neg_mul_neg,← mul_assoc,hv,one_mul]
lemma fireplace (h:Flash L T) : Dilation T⁻¹ := by
  constructor; intro i
  induction i using Nat.caseStrongRecOn with
  | zero=> simpa only [LitP,Nat.add_zero] using (blazing h).1
  | ind n ih=>
    intro b v; rw [invert_coin (recoupC h),Matrix.mul_apply]
    intro he; obtain ⟨x,hx,hy⟩:=exists_ne_zero_of_sum_ne_zero he
    obtain ⟨hz,hW⟩:=mul_ne_zero_iff.mp hy; rw [Matrix.sum_apply] at hW
    obtain ⟨j,hj,hY⟩:= exists_ne_zero_of_sum_ne_zero hW; obtain ⟨hE,hj⟩:= mem_filter.mp hj; have hm:=mem_antidiagonal.mp hE
    rw [Matrix.mul_apply] at hY; obtain ⟨a,ha,hA⟩:= exists_ne_zero_of_sum_ne_zero hY
    obtain ⟨hC,H⟩:=mul_ne_zero_iff.mp hA; have ht:= h.stairs _ _ _ hC; have hg:= ih j.2 (by omega) _ _ H
    have hu:= (blazing h).1 _ _ (show hot T⁻¹ 0 b x ≠0 by simpa using hz); omega
end YM.RG08.Needle
