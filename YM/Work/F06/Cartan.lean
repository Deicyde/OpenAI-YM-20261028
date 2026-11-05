import YM.Exterior.Blade

/-!
# A coordinate contraction for the initial-corner convention

For a nonzero component `q k`, use just contraction with the k-th
basis element. Thus we need the algebraic Cartan identity, not any
unitary change of frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F06
open Exterior Matrix Finset
open scoped BigOperators

variable {α R : Type*} [LinearOrder α] {r : ℕ}

/-- Insert a missing axis into a sorted blade. -/
def addAxis (k : α) (b : Blade α r) (h : k ∉ b.val) : Blade α (r+1) :=
  ⟨insert k b.val, by rw [card_insert_of_notMem h, b.property]⟩

lemma mem_addAxis (k : α) (b : Blade α r) (h) : k ∈ (addAxis k b h).val :=
  mem_insert_self ..

lemma notMem_cut (k : α) (b : Blade α (r+1)) (h) : k ∉ (Exterior.remove k b h).val := by
  simp [Exterior.remove]

lemma remove_addAxis (k : α) (b : Blade α r) (h) :
    Exterior.remove k (addAxis k b h) (mem_addAxis k b h) = b := by
  apply Subtype.ext
  simp [Exterior.remove, addAxis, h]

lemma addAxis_remove (k : α) (b : Blade α (r+1)) (h) :
    addAxis k (Exterior.remove k b h) (notMem_cut k b h) = b := by
  apply Subtype.ext
  simp [Exterior.remove, addAxis, h]

lemma parity_square [CommRing R] (S : Finset α) (i : α) :
    parity S i R * parity S i R = 1 := by
  unfold parity
  rw [← mul_pow]
  simp

variable [CommRing R] [Fintype α]

/-- `eliminate` for the transpose instead of the wedge. -/
lemma eliminate_transpose (v : Blade α (r+1) → R) (b : Blade α r) (k : α) :
    ((left R r k).transpose *ᵥ v) b = if h : k ∉ b.val then
      parity (addAxis k b h).val k R * v (addAxis k b h) else 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  by_cases hk : k ∉ b.val
  · rw [dif_pos hk, Finset.sum_eq_single (addAxis k b hk)]
    · simp [Exterior.left, mem_addAxis, remove_addAxis]
    · intro a _ ha
      by_cases he : k ∈ a.val
      · have hu : Exterior.remove k a he ≠ b := by
          intro h
          apply ha
          apply Subtype.ext
          change a.val = insert k b.val
          rw [← h]; simp [Exterior.remove, he]
        simp [Exterior.left, he, hu]
      simp [Exterior.left, he]
    simp
  rw [dif_neg hk]
  apply Finset.sum_eq_zero
  intro a _
  by_cases he : k ∈ a.val
  · have hu : Exterior.remove k a he ≠ b := by
      intro h
      apply hk
      rw [← h]; exact notMem_cut k a he
    simp [Exterior.left, he, hu]
  simp [Exterior.left, he]

-- Common sign cancellation for swapping inserted and deleted axes.
omit [Fintype α] in
lemma parity_swap (S : Finset α) {j k : α} (hj : j ∈ S) (hk : k ∈ S) (hne : j ≠ k) :
    parity (S.erase k) j R * parity (S.erase j) k R +
      parity S k R * parity S j R = 0 := by
  unfold parity
  rcases lt_or_gt_of_ne hne with h|h
  · rw [pre_lo S h.le, ← pre_hi S h hj, pow_succ]
    ring
  rw [pre_lo S h.le, ← pre_hi S h hk, pow_succ]; ring

lemma cartan_axis (v : Blade α (r+1) → R) (j k : α) :
    left R r j *ᵥ ((left R r k).transpose *ᵥ v) +
      (left R (r+1) k).transpose *ᵥ (left R (r+1) j *ᵥ v) =
        if j = k then v else 0 := by
  funext b
  rw [Pi.add_apply, eliminate, eliminate_transpose]
  by_cases he : j = k
  · subst k
    rw [if_pos rfl]
    by_cases hj : j ∈ b.val
    · rw [dif_pos hj, dif_neg (not_not.mpr hj), add_zero, eliminate_transpose,
        dif_pos (notMem_cut j b hj), addAxis_remove, ← mul_assoc, parity_square, one_mul]
    rw [dif_neg hj, dif_pos hj, zero_add, eliminate, dif_pos (mem_addAxis j b hj),
      remove_addAxis, ← mul_assoc, parity_square, one_mul]
  rw [if_neg he, Pi.zero_apply]
  by_cases hj : j ∈ b.val
  · rw [dif_pos hj, eliminate_transpose]
    by_cases hk : k ∉ b.val
    · have hc : k ∉ (Exterior.remove j b hj).val := by simp [Exterior.remove, hk]
      have hd : j ∈ (addAxis k b hk).val := by simp [addAxis, hj]
      rw [dif_pos hk, dif_pos hc, eliminate, dif_pos hd]
      have hs : addAxis k (Exterior.remove j b hj) hc =
          Exterior.remove j (addAxis k b hk) hd := by
        apply Subtype.ext; ext i
        by_cases hi : i = k <;> simp [Exterior.remove, addAxis, hi, Ne.symm he]
      rw [hs, ← mul_assoc, ← mul_assoc, ← add_mul]
      have hp := parity_swap (R:=R) _ hd (mem_addAxis k b hk) he
      rw [show ((addAxis k b hk).val.erase k) = b.val
        from congrArg Subtype.val (remove_addAxis k b hk)] at hp
      change parity b.val j R * parity (Exterior.remove j (addAxis k b hk) hd).val k R +
        parity (addAxis k b hk).val k R * parity (addAxis k b hk).val j R = 0 at hp
      rw [hp, zero_mul]
    have hc : ¬ k ∉ (Exterior.remove j b hj).val := by
      have hk' : k ∈ b.val := not_not.mp hk
      simp [Exterior.remove, hk', Ne.symm he]
    rw [dif_neg hk, dif_neg hc]; simp
  rw [dif_neg hj]
  by_cases hk : k ∉ b.val
  · have hc : j ∉ (addAxis k b hk).val := by simp [addAxis, he, hj]
    rw [dif_pos hk, eliminate, dif_neg hc]; simp
  rw [dif_neg hk]; simp

lemma cartan (v : Blade α (r+1) → R) (z : α → R) (k : α) :
    wedge r z *ᵥ ((left R r k).transpose *ᵥ v) +
      (left R (r+1) k).transpose *ᵥ (wedge (r+1) z *ᵥ v) = z k • v := by
  unfold wedge
  simp_rw [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sum,
    Matrix.mulVec_smul, ← Finset.sum_add_distrib, ← smul_add,
    cartan_axis v _ k]
  simp [smul_ite]

/-- Split into a genuine range vector plus a term controlled by the next symbol.
This need not be an orthogonal decomposition. -/
lemma cartan_split (v : Blade α (r+1) → ℂ) (z : α → ℂ) (k : α) (hk : z k ≠ 0) :
    v = wedge r z *ᵥ ((z k)⁻¹ • ((left ℂ r k).transpose *ᵥ v)) +
      (z k)⁻¹ • ((left ℂ (r+1) k).transpose *ᵥ (wedge (r+1) z *ᵥ v)) := by
  rw [Matrix.mulVec_smul, ← smul_add, cartan, smul_smul, inv_mul_cancel₀ hk, one_smul]

end YM.Work.F06
