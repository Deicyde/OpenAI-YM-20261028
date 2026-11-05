import YM.MultiNext.VACUUM_STABILITY.Sums

set_option warningAsError false

/-!
# Deletion identity for the first unforced system

This is the ordinary complex gas, before any projection to markers. Addresses are actual
labels, compatibility is disjointness on their complete support, letters may cancel.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Vacuum.BulkGas
open RG Lattice Wilson Filter Finset Function MeasureTheory Corona
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I : Type} {n : Side}

def admits (X : I → Support n) (R : Support n) (B : Finset I) :=
    (B : Set I).PairwiseDisjoint X ∧ ∀ i ∈ B, X i ⊆ R

abbrev Pass (X : I → Support n) (R : Support n) := {B : Finset I // admits X R B}

def earning (u : I → ℂ) (B : Finset I) := ∏ i ∈ B, u i

def Z (X : I → Support n) (R : Support n) (u : I → ℂ) := ∑' B : Pass X R, earning u B.val

lemma absolute (X : I → Support n) {u : I → ℂ} (h : Summable fun i => ‖u i‖) (R : Support n) :
    Summable (fun B : Pass X R => ‖earning u B.val‖) :=
  ((summable_finsetProd_of_summable_norm h).norm).subtype _

section
variable {X : I → Support n} {R : Support n} {x : Site n}

abbrev Face (X : I → Support n) (R : Support n) (x : Site n) :=
    {i : I // x ∈ X i ∧ X i ⊆ R}

private abbrev Aside (X : I → Support n) (R : Support n) (x : Site n) := Pass X (R.erase x)
private abbrev Claim (X : I → Support n) (R : Support n) (x : Site n) :=
    Σ i : Face X R x, Pass X (R \ X i.val)

private def invite (s : Aside X R x) : Pass X R := ⟨s.val,s.property.1,
    fun i hi => subset_trans (s.property.2 i hi) (erase_subset ..)⟩

private lemma dispute (B : Aside X R x) {i : I} (hi : i ∈ B.val) : x ∉ X i :=
  fun h => Finset.notMem_erase x R (B.property.2 i hi h)

private lemma unity (B : Pass X R) {i j : I} (hi : i ∈ B.val) (hj : j ∈ B.val)
    (hx : x ∈ X i) (hy : x ∈ X j) : i = j := by
  by_contra hh; exact Finset.disjoint_left.mp (B.property.1 hi hj hh) hx hy

private lemma countermand (s : Claim X R x) : s.1.val ∉ s.2.val := by
  intro h
  exact ((Finset.mem_sdiff.mp (s.2.property.2 _ h s.1.property.1)).2 s.1.property.1)

private def includeClaim (s : Claim X R x) : Pass X R := by
  obtain ⟨⟨i,hi,hB⟩,⟨A,hAd,hA⟩⟩ := s
  refine ⟨insert i A, ?_, ?_⟩
  · intro j hj k hk he
    rw [mem_coe, mem_insert] at hj hk
    obtain rfl|h₁ := hj <;> obtain rfl|h₂ := hk
    · contradiction
    · exact (Finset.subset_sdiff.mp (hA k h₂)).2.symm
    · exact (Finset.subset_sdiff.mp (hA j h₁)).2
    exact hAd h₁ h₂ he
  intro j hj; obtain rfl|h₁ := mem_insert.mp hj
  · exact hB
  exact (Finset.subset_sdiff.mp (hA j h₁)).1

private lemma include_read (s : Claim X R x) : (includeClaim s).val = insert s.1.val s.2.val := by
  rcases s with ⟨⟨i,h,g⟩,⟨B,hs,hb⟩⟩; rfl

private lemma inject_claim (X : I → Support n) (R : Support n) (x : Site n) : Injective (includeClaim (X:=X) (R:=R) (x:=x)) := by
  intro s t hh
  have hi (s : Claim X R x) : s.1.val ∈ (includeClaim s).val := by rw [include_read]; exact mem_insert_self ..
  have he := unity _ (hh ▸ hi s) (hi t) s.1.property.1 t.1.property.1
  have ha : s.1=t.1 := Subtype.ext he
  have h : insert s.1.val s.2.val = insert t.1.val t.2.val := (include_read s).symm.trans <|
      (congrArg Subtype.val hh).trans (include_read t)
  have h' := countermand s; have ht := countermand t
  obtain ⟨i,A⟩ := s; obtain ⟨j,B⟩ := t
  simp only at *; subst j
  refine congrArg (Sigma.mk i) (Subtype.ext ?_)
  simpa [Finset.erase_insert h', Finset.erase_insert ht] using congrArg (fun D : Finset I => D.erase i.val) h

private lemma hire (s : Claim X R x) (t : Aside X R x) : includeClaim s ≠ invite t := by
  intro h
  apply dispute t (i:=s.1.val) _ s.1.property.1
  change _ ∈ (invite t).val; rw [← h,include_read]; exact mem_insert_self ..

private lemma doors (s : Pass X R) : (∃ A : Aside X R x, invite A = s) ∨ (∃ B : Claim X R x, includeClaim B = s) := by
  by_cases h : ∃ i ∈ s.val, x ∈ X i
  · obtain ⟨i,hi,hx⟩ := h
    let A : Face X R x := ⟨i,hx,s.property.2 i hi⟩
    have he : admits X (R \ X i) (s.val.erase i) := by
      constructor
      · intro j hj k hk HH
        exact s.property.1 (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) HH
      intro j hj
      obtain ⟨hb,ht⟩ := Finset.mem_erase.mp hj
      exact Finset.subset_sdiff.mpr ⟨s.property.2 j ht,s.property.1 ht hi hb⟩
    right; refine ⟨⟨A,s.val.erase i, he⟩, Subtype.ext ?_⟩; rw [include_read]; exact insert_erase hi
  left
  exact ⟨⟨s.val,s.property.1,fun i hi _ hx => mem_erase.mpr ⟨fun he => h ⟨i,hi,he ▸ hx⟩, s.property.2 i hi hx⟩⟩,Subtype.ext rfl⟩

private def tickets (X : I → Support n) (R : Support n) (x : Site n) : Aside X R x ⊕ Claim X R x ≃ Pass X R := by
  refine Equiv.ofBijective (Sum.elim invite includeClaim) ⟨?_, ?_⟩
  · rintro (s|s) (t|t) he
    · have ht := congrArg Subtype.val (show invite s=invite t from he)
      exact congrArg Sum.inl (Subtype.ext (show s.val=t.val from ht))
    · exact False.elim (hire t s he.symm)
    · exact False.elim (hire s t he)
    exact congrArg Sum.inr (inject_claim X R x he)
  intro s; obtain ⟨a,ha⟩|⟨a,ha⟩ := doors (x:=x) s
  · exact ⟨Sum.inl a,ha⟩
  exact ⟨Sum.inr a,ha⟩

/-- True deletion identity (also trivial case x not in R). Nonempty supports of hitting
addresses implicit from the hit. Used with all addresses nonempty for log recursion. -/
lemma delete (X : I → Support n) (R : Support n) (x : Site n) {u : I → ℂ}
    (h : Summable fun i => ‖u i‖) : Z X R u = Z X (R.erase x) u +
      ∑' i : Face X R x, u i.val * Z X (R \ X i.val) u := by
  let A (s : Pass X R) := earning u s.val
  let e := tickets X R x
  have hf : Summable (A ∘ e) := Equiv.summable_iff e |>.mpr (absolute X h R).of_norm
  let f := A ∘ e
  have hg : Summable f := hf
  have hr : Summable (fun i : Claim X R x => f (Sum.inr i)) := hg.comp_injective Sum.inr_injective
  rw [Z, show (∑' i,A i)=(∑' i,f i) from (e.tsum_eq _).symm,
    Absolute.union_tsum (hg.comp_injective Sum.inl_injective) hr]
  congr 1
  rw [hr.tsum_sigma]; refine tsum_congr fun i => ?_
  unfold Z; rw [← tsum_mul_left]; refine tsum_congr fun j => ?_
  change earning u (includeClaim ⟨i,j⟩).val=u _* earning u j.val
  unfold earning; rw [include_read]; exact Finset.prod_insert (countermand ⟨i,j⟩)

lemma vacant (X : I → Support n) (h : ∀ i, (X i).Nonempty) (u : I → ℂ) :
    Z X ∅ u = 1 := by
  let b : Pass X ∅ := ⟨∅,by simp [admits]⟩
  unfold Z; rw [tsum_eq_single b]; rfl
  intro j hj; exfalso
  have hz : j.val ≠ ∅ := fun H => hj (Subtype.ext H)
  obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hz
  obtain ⟨i, hi⟩ := h x; simpa using j.property.2 x hx hi

lemma Z_eq (X : I → Support n) (R : Support n) (u : I → ℂ) : Z X R u =
    ∑' B, if admits X R B then earning u B else 0 := by
  unfold Z
  refine Eq.trans (tsum_subtype (s:=setOf (admits X R)) _) ?_
  refine tsum_congr fun x => ?_; by_cases h : admits X R x <;> simp [Set.indicator,h]

lemma restrict (X : I → Support n) (R : Support n) (u : I → ℂ) : Z X R u =
    Z X Finset.univ (fun i => if X i ⊆ R then u i else 0) := by
  simp_rw [Z_eq]; refine tsum_congr fun b => ?_
  by_cases h : (b : Set I).PairwiseDisjoint X
  · simp only [admits,h,true_and,Finset.subset_univ,implies_true,if_true]
    split
    · rename_i hh; exact prod_congr rfl fun i hi => (if_pos (hh i hi)).symm
    rename_i hh; push Not at hh
    obtain ⟨i,hi,hr⟩ := hh
    exact (Finset.prod_eq_zero hi (if_neg hr)).symm
  simp [admits,h]
end
end YM.Multi.Vacuum.BulkGas
