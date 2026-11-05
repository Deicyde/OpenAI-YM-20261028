import YM.Push.LOOP_COEFFICIENT.Pullback

/-!
# One-coordinate exterior homotopy: wedge vs bilinear contraction
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Finset Function Matrix Exterior
open scoped BigOperators
variable {d : Type} [LinearOrder d] {r : ℕ} (K : Type) [CommRing K]

def adjoin (i : d) (S : Blade d r) (h : i ∉ S.val) : Blade d (r+1) := ⟨insert i S.val,by rw [card_insert_of_notMem h, S.property]⟩
lemma adjoin_mem {i : d} {S : Blade d r} (h : i∉S.val) : i∈(adjoin i S h).val := mem_insert_self ..
lemma remove_adjoin {i : d} {S : Blade d r} (h : i∉S.val) : remove i _ (adjoin_mem h) = S := Subtype.ext (Finset.erase_insert h)
lemma parity_mul (i : d) (S : Finset d) : parity S i K * parity S i K = 1 := by unfold parity; rw [← mul_pow]; simp

variable [Fintype d]
lemma wedge_axis (i : d) (S : Blade d (r+1)) {w : Blade d r → K} :
    (left K r i *ᵥ w) S = if h : i ∈ S.val then parity S.val i K * w (remove i S h) else 0 := eliminate ..
lemma dual_axis (i : d) (S : Blade d r) {w : Blade d (r+1) → K} :
    ((left K r i).transpose *ᵥ w) S = if h : i∈S.val then 0 else parity (insert i S.val) i K * w (adjoin i S h) := by
  split
  next hi =>
    apply Finset.sum_eq_zero; intro b _; dsimp only; rw [transpose_apply,left,of_apply]; split
    next h => rw [if_neg (fun he => (notMem_erase i b.val) (show i∈(remove i b h).val by rwa [he])),zero_mul]
    rw [zero_mul]
  next h =>
    unfold Matrix.mulVec dotProduct; simp only [transpose_apply,left,of_apply]; rw [Fintype.sum_eq_single (adjoin i S h),dif_pos (adjoin_mem h),if_pos (remove_adjoin h)]; rfl
    intro b hb; split
    next hi => rw [if_neg (fun he => hb (Subtype.ext (by change b.val=insert i S.val; rw [← he]; exact (insert_erase hi).symm))),zero_mul]
    rw [zero_mul]
lemma diag_axis (i : d) (S : Blade d (r+1)) (w : Blade d (r+1) → K) :
    (left K r i *ᵥ ((left K r i).transpose *ᵥ w)) S = if i∈S.val then w S else 0 := by
  rw [wedge_axis]; split
  next h =>
    rw [dual_axis,dif_neg (show i ∉ (remove i S h).val from notMem_erase i S.val),show insert i (remove i S h).val = S.val from insert_erase h,
      show adjoin i (remove i S h) _ = S from Subtype.ext (insert_erase h), ← mul_assoc, parity_mul,one_mul]
  next _ => rfl
lemma diag_coaxis (i : d) (S : Blade d r) (w : Blade d r → K) :
    ((left K r i).transpose *ᵥ (left K r i *ᵥ w)) S = if i ∈ S.val then 0 else w S := by
  rw [dual_axis]; split
  next _ => rfl
  next h => rw [wedge_axis,dif_pos (adjoin_mem h), remove_adjoin h,← mul_assoc,adjoin, parity_mul,one_mul]

lemma wedge_dual_off (i j : d) (h : j ≠ i) (S : Blade d (r+1)) (w : Blade d (r+1) → K) :
    ((left K (r+1) j).transpose *ᵥ left K (r+1) i *ᵥ w) S = -(left K r i *ᵥ (left K r j).transpose *ᵥ w) S := by
  rw [wedge_axis]; split <;> rename_i hi
  · rw [dual_axis,dual_axis]; split <;> rename_i hj
    · simp [remove,hj,h]
    have he : j ∉ (remove i S hi).val := by simp [remove,hj]
    have he' : i∈(adjoin j S hj).val := mem_insert_of_mem hi
    rw [dif_neg he,wedge_axis,dif_pos he',show remove i (adjoin j S hj) he' = adjoin j (remove i S hi) he by ext; simp [remove,adjoin]; aesop,
      ← mul_assoc,← mul_assoc,← neg_mul]
    congr 1
    rcases lt_or_gt_of_ne h with h'|h'
    · have h1 := pre_hi (insert j S.val) h' (mem_insert_self ..); rw [erase_insert hj] at h1
      have h2 : pre (insert j (S.val.erase i)) j = pre (insert j S.val) j := by
        rw [show insert j (S.val.erase i) = (insert j S.val).erase i by ext; simp; aesop]; exact pre_lo _ h'.le
      simp only [parity,adjoin,remove,h2,← h1,pow_succ]; ring
    have h1 := pre_lo (insert j S.val) h'.le; rw [erase_insert hj] at h1
    have h2 : pre (insert j (S.val.erase i)) j+1 = pre (insert j S.val) j := by
      rw [show insert j (S.val.erase i) = (insert j S.val).erase i by ext; simp; aesop]; exact pre_hi _ h' (mem_insert_of_mem hi)
    rw [mul_comm]; simp only [parity,adjoin,remove,← h1,← h2,pow_succ]; ring
  · rw [neg_zero,dual_axis]; split; rfl
    rw [wedge_axis,dif_neg (by simp [adjoin,Ne.symm h,hi]),mul_zero]
lemma wedge_dual (q : d → K) (i : d) (w : Blade d (r+1) → K) :
    (wedge (r+1) q).transpose *ᵥ (left K (r+1) i *ᵥ w) + left K r i *ᵥ ((wedge r q).transpose *ᵥ w) = q i • w := by
  simp only [wedge,transpose_sum,Matrix.sum_mulVec,Matrix.transpose_smul,Matrix.smul_mulVec,Matrix.mulVec_sum,Matrix.mulVec_smul,← sum_add_distrib,← smul_add]; ext S; rw [Finset.sum_apply, Fintype.sum_eq_single i]
  · rw [Pi.smul_apply,Pi.add_apply,diag_axis,diag_coaxis]; split <;> simp
  intro j hj
  simp only [Pi.smul_apply, Pi.add_apply, wedge_dual_off K i j hj,neg_add_cancel,smul_zero]
end YM.Push.Loops
