import YM.Push.LOOP_COEFFICIENT.Ghost
import YM.Work.F05.Reindex

/-!
# Free split determinant

A fine gauge parameter per site, constrained joint slots are actual positive
tree links plus coarse frame sites. No assumptions on chronological ordering of
the physical matrix indices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Lattice Wilson RG Precision Tree Matrix Function
open scoped Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f} {g : Ratio c f}

def fixedSlot (B : Forest g) (x : Site f) : Joint c f := if leaf g x then
  Sum.inl ((B.up x).used x) else Sum.inr (g.parent x)

def slotOrder (B : Forest g) : (Site f ⊕ B.Free) ≃ Joint c f := by
  let F : (Site f ⊕ B.Free) → Joint c f := Sum.elim (fixedSlot B) (fun i => Sum.inl i.val)
  have h1 (x) (hx : leaf g x) : F (.inl x) = Sum.inl (Work.F05.pinEquiv B ⟨x,hx⟩).val := if_pos hx
  have h2 (x) (hx : ¬leaf g x) : F (.inl x) = Sum.inr (g.parent x) := if_neg hx
  refine Equiv.ofBijective F ⟨fun i j hi => ?_,fun a => ?_⟩
  · cases i with
    | inl i =>
      cases j with
      | inl j =>
        by_cases h : leaf g i <;> by_cases h' : leaf g j
        · rw [h1 _ h,h1 _ h'] at hi
          exact congr_arg Sum.inl (congr_arg Subtype.val ((Work.F05.pinEquiv B).injective (Subtype.ext (Sum.inl.inj hi))))
        · rw [h1 _ h,h2 _ h'] at hi; contradiction
        · rw [h2 _ h,h1 _ h'] at hi; contradiction
        · rw [h2 _ h,h2 _ h'] at hi; congr 1
          exact (Classical.not_not.mp h).trans ((congr_arg g.embed (Sum.inr.inj hi)).trans (Classical.not_not.mp h').symm)
      | inr j =>
        by_cases h : leaf g i
        · rw [h1 _ h] at hi
          exact (j.property ((Sum.inl.inj hi) ▸ (Work.F05.pinEquiv B ⟨i,h⟩).property)).elim
        rw [h2 _ h] at hi; contradiction
    | inr i =>
      cases j with
      | inl j =>
        by_cases h : leaf g j
        · rw [h1 _ h] at hi
          exact (i.property ((Sum.inl.inj hi).symm ▸ (Work.F05.pinEquiv B ⟨j,h⟩).property)).elim
        rw [h2 _ h] at hi; contradiction
      | inr j => exact congr_arg Sum.inr (Subtype.ext (Sum.inl.inj hi))
  · cases a with
    | inl a =>
      by_cases h : a∈B.trunks
      · obtain ⟨i,hi⟩ := (Work.F05.pinEquiv B).surjective ⟨a,h⟩
        exact ⟨.inl i.val, (h1 _ i.property).trans (congr_arg (fun x : ↥B.trunks => Sum.inl x.val) hi)⟩
      exact ⟨.inr ⟨a,h⟩,rfl⟩
    | inr a =>
      exact ⟨.inl (g.embed a),by rw [h2 _ (by simp [leaf,g.embed_parent]),g.embed_parent]⟩

def pins (B : Forest g) (G : Gauge) : (SiteKey G f ⊕ Key B G) ≃ JointKey G c f :=
  (Equiv.sumProdDistrib _ _ _).symm.trans (Equiv.prodCongr (slotOrder B) (Equiv.refl G.ColorIndex))




/-- A block lower triangular matrix with ±1 on the diagonal and no
same-height off-diagonal entries. -/
private lemma triangle_det {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (b : n → ℕ)
    (ha : ∀ i j, b i ≤ b j → |A i j| = if i=j then (1:ℝ) else 0) : |A.det| = 1 := by
  have hz i j (h : b i ≤ b j) (he : i≠j) : A i j=0 := abs_eq_zero.mp ((ha i j h).trans (if_neg he))
  have hh : A.transpose.BlockTriangular b := fun i j h => hz j i h.le (fun he => h.ne (congr_arg b he))
  rw [← det_transpose, hh.det, Finset.abs_prod]
  refine Finset.prod_eq_one (fun k _ => ?_)
  rw [show A.transpose.toSquareBlock b k = diagonal (fun i => A i.val i.val) by
    ext i j; change A j.val i.val = _
    rw [diagonal_apply]; split
    · rename_i h; rw [h]
    exact hz _ _ (j.property.trans i.property.symm).le (fun he => ‹i≠j› (Subtype.ext he.symm)), det_diagonal,Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => (ha i.val i.val le_rfl).trans (if_pos rfl)

/-- Counting determinant on constrained rows (tree links at one, actual
orientation may point towards or away from parent in storage). -/
lemma pins_det (B : Forest S.ratio) (U : Loops.Inputs G c f)
    (hf : ∀ x, U (fixedSlot B x) = 1) : |((R_tot S U).submatrix (pins B G ∘ Sum.inl) id).det| = 1 := by
  refine triangle_det _ (fun p => B.height p.1) (fun ⟨i,a⟩ ⟨j,b⟩ hij => ?_)
  change B.height i ≤ B.height j at hij
  let v : Nodes G f := Pi.single (j,b) 1
  change |paint G _ (braceJoint S U v) (fixedSlot B i) a| = if (i,a)=(j,b) then 1 else 0
  unfold fixedSlot
  split_ifs with h he he
  · rw [Prod.mk.injEq] at he; obtain ⟨rfl,rfl⟩ := he
    rw [paint_braceJoint_left,paint_brace, show positions U ((B.up i).used i)=1 by simpa only [positions, Function.comp_apply,fixedSlot,if_pos h] using hf i, G.adjoint_one]
    have hr := B.rise i h
    have hi : i + (B.up i).vec ≠ i := fun e => hr.ne (congr_arg B.height e)
    cases e : (B.up i).neg
    · rw [Step.vec, if_neg (show (B.up i).neg ≠ true from by simp [e])] at hi; simp [e,v,Step.used,hi]
    rw [Step.vec,if_pos e,← sub_eq_add_neg] at hi; simp [Step.used, e,v,hi]
  · rw [paint_braceJoint_left,paint_brace, show positions U ((B.up i).used i)=1 by simpa only [positions, Function.comp_apply,fixedSlot,if_pos h] using hf i, G.adjoint_one]
    have hi : i + (B.up i).vec ≠ j := fun e => (lt_of_lt_of_le (B.rise i h) hij).ne (congr_arg B.height e)
    simp only [Prod.mk.injEq] at he
    cases e : (B.up i).neg
    · rw [Step.vec,if_neg (show (B.up i).neg ≠ true by simp [e])] at hi; simp [Step.used,e,v,he,hi]
    rw [Step.vec,if_pos e,← sub_eq_add_neg] at hi; simp [Step.used,e,v,he,hi]
  · rw [paint_braceJoint_right, show auxiliaries U (S.ratio.parent i) = 1 by simpa only [auxiliaries, Function.comp_apply, fixedSlot, if_neg h] using hf i,
      G.adjoint_one,← Classical.not_not.mp h]
    simp [v,he]
  rw [paint_braceJoint_right, show auxiliaries U (S.ratio.parent i) = 1 by simpa only [auxiliaries, Function.comp_apply, fixedSlot, if_neg h] using hf i,
    G.adjoint_one,← Classical.not_not.mp h]
  simp only [Prod.mk.injEq] at he
  simp [v,he]
end YM.Push.Loops
