import YM.Next.RANK.EntryWord

/-! Expansion and support restart from full-torus insertion correction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.EntryWord
open Lattice Wilson RG Finset MeasureTheory Marker Value Glyph
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] [Fintype V] {ζ : V → Site n} {τ : ℝ}
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable (K : ι → Lifted G ζ τ) (F : κ → Refusal G ζ τ)

omit [DecidableEq ι] [DecidableEq κ] in
lemma area_nonempty (i : ι ⊕ κ) : (area K F i).Nonempty := by
  cases i with
  | inl i => exact (K i).needed.mono (K i).records
  | inr i => obtain ⟨v,h⟩ := (F i).chosen; exact ⟨_,(F i).remembers v h⟩

def unhook (s : Finset (Latch K F)) := s.biUnion Subtype.val
private lemma unhook_here (s : Finset (Latch K F)) :
    (s.image Subtype.val).biUnion id = unhook K F s := by
  ext; simp [unhook]

omit [DecidableEq ι] [DecidableEq κ] in
private lemma disjointLatch (s : Finset (Latch K F)) (h : (s:Set _).PairwiseDisjoint (keep K F)) :
    (s : Set (Latch K F)).PairwiseDisjoint Subtype.val := by
  intro i hi j hj he; apply disjoint_left.mpr
  intro a hai haj; obtain ⟨x,hx⟩ := area_nonempty K F a
  exact disjoint_left.mp (h hi hj he) (mem_biUnion.mpr ⟨a,hai,hx⟩) (mem_biUnion.mpr ⟨a,haj,hx⟩)
private lemma hooked (s : Finset (Latch K F)) (h : (s:Set _).PairwiseDisjoint (keep K F)) :
    Ac.Parts (area K F) (unhook K F s) = s.image Subtype.val := by
  rw [← unhook_here]; apply Ac.separates
  · intro i hi; obtain ⟨p,_,rfl⟩ := mem_image.mp hi; exact p.property.1
  intro i hi j hj hh; obtain ⟨p,hp,rfl⟩ := mem_image.mp hi; obtain ⟨q,hq,rfl⟩ := mem_image.mp hj
  exact h hp hq fun he => hh (he ▸ rfl)

lemma counted (U : Config G n) (s : Finset (Latch K F)) (hg : Lifted.gather (merged K F) s U) :
    Lifted.pack (merged K F) s U = cube K F (unhook K F s) U := by
  have h : (s:Set _).PairwiseDisjoint (keep K F) := hg.1
  rw [Lifted.pack, if_pos hg,cube, unhook, prod_biUnion (disjointLatch K F s h)]
  apply prod_congr rfl
  intro i hi; rw [look_inside K F i U]
  have he : s.biUnion (owns K F)=flags τ U := hg.2
  have hv : keep K F i ∩ flags τ U=owns K F i := by
    rw [← he]; ext x; rw [mem_inter]; constructor
    · rintro ⟨hp,hx⟩; obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hx
      obtain rfl := (show i=j from Classical.byContradiction fun ht => disjoint_left.mp (h hi hj ht) hp (held K F j hx)); exact hx
    intro hn; exact ⟨held K F i hn, mem_biUnion.mpr ⟨_,hi,hn⟩⟩
  rw [if_pos hv]; rfl

-- reconstruct inverse map on all terms potentially nonzero

private lemma roll (s : Finset (Latch K F)) :
    ((unhook K F s).toLeft.biUnion (fun i => (K i).inventory))=s.biUnion (owns K F) := by
  ext x; simp only [mem_biUnion]; constructor
  · rintro ⟨i,hi,hx⟩; obtain ⟨p,hp,h⟩ := mem_biUnion.mp (mem_toLeft.mp hi); exact ⟨p,hp,mem_biUnion.mpr ⟨i,mem_toLeft.mpr h,hx⟩⟩
  rintro ⟨i,hi,he⟩; obtain ⟨p,hp,h⟩ := mem_biUnion.mp he; exact ⟨p,mem_toLeft.mpr (mem_biUnion.mpr ⟨i,hi,mem_toLeft.mp hp⟩),h⟩

def sailed (U : Config G n) (s : Finset (ι ⊕ κ)) := Lifted.gather K s.toLeft U ∧ grabs K F s

private lemma on (s : Finset (Latch K F)) (U) (hg : Lifted.gather (merged K F) s U) : sailed K F U (unhook K F s) := by
  have h : (s:Set _).PairwiseDisjoint (keep K F) := hg.1; refine ⟨⟨?_, (roll K F s).trans hg.2⟩,?_⟩
  · intro i hi j hj he; obtain ⟨p,hp,h'⟩ := mem_biUnion.mp (mem_toLeft.mp hi)
    obtain ⟨q,hq,hq'⟩ := mem_biUnion.mp (mem_toLeft.mp hj)
    rcases eq_or_ne p q with rfl|hn
    · exact p.property.2.2.1 (mem_toLeft.mpr h') (mem_toLeft.mpr hq') he
    exact disjoint_left.mpr fun x hx he' =>
      disjoint_left.mp (h hp hq hn) (mem_biUnion.mpr ⟨.inl i,h',hx⟩) (mem_biUnion.mpr ⟨.inl j,hq',he'⟩)
  intro i hi; obtain ⟨j,hj,h⟩ := mem_biUnion.mp (mem_toRight.mp hi)
  obtain ⟨p,hp,he⟩ := j.property.2.2.2 i (mem_toRight.mpr h); exact ⟨p,mem_toLeft.mpr (mem_biUnion.mpr ⟨j,hj,mem_toLeft.mp hp⟩),he⟩

private lemma all_to (U : Config G n) (q : Finset (ι ⊕ κ)) (hq : sailed K F U q) :
    ∃ s : Finset (Latch K F), Lifted.gather (merged K F) s U ∧ unhook K F s=q := by
  let X := area K F
  let T := Ac.Parts X q
  have hp {p} (hi : p∈ T) : locks K F p := by
    obtain ⟨h,hn⟩ := Ac.lives X q hi
    have hg : grabs K F p := by
      intro i ht
      obtain ⟨j,hj,he⟩ := hq.2 i (toRight_subset_toRight h ht)
      refine ⟨j,mem_toLeft.mpr ?_,he⟩
      obtain ⟨x,hx,hk⟩ := Finset.not_disjoint_iff.mp he
      have hz : Ac.chain X q (.inr i) (.inl j) := .single ⟨h (mem_toRight.mp ht), mem_toLeft.mp hj,x,hk,hx⟩
      rw [← Ac.contains X hi _ (mem_toRight.mp ht)]; exact (Ac.bright ..).mpr ⟨mem_toLeft.mp hj,hz⟩
    refine ⟨hn,?_,fun a ha b hb => hq.1.1 (toLeft_subset_toLeft h ha) (toLeft_subset_toLeft h hb),hg⟩
    obtain ⟨i|i,hi⟩ := hn.1
    · exact ⟨i,mem_toLeft.mpr hi⟩
    obtain ⟨j,hj,-⟩ := hg i (mem_toRight.mpr hi); exact ⟨j,hj⟩
  let s : Finset (Latch K F) := T.preimage Subtype.val Subtype.val_injective.injOn
  have he : s.image Subtype.val=T := by
    ext i; constructor
    · intro H; obtain ⟨x,hx,rfl⟩ := mem_image.mp H; exact mem_preimage.mp hx
    intro H; refine mem_image.mpr ⟨⟨i,hp H⟩,mem_preimage.mpr H,rfl⟩
  have hu : unhook K F s=q := by rw [← unhook_here,he]; exact Ac.reconstruct X q
  refine ⟨s,⟨fun i hi j hj hn => ?_,?_⟩,hu⟩
  · exact Ac.separate X q (mem_preimage.mp hi) (mem_preimage.mp hj) fun he => hn (Subtype.ext he)
  exact (roll K F s).symm.trans (by rw [hu]; exact hq.1.2)

omit [DecidableEq ι] [DecidableEq κ] in
private lemma needs (s : Finset (ι ⊕ κ)) (U) (h : Lifted.gather K s.toLeft U) (hf : cube K F s U≠0) : grabs K F s := by
  intro i hi
  have hh : (F i).value U ≠ 0 := fun hz => hf (prod_eq_zero (mem_toRight.mp hi) (show hook K F _ U = 0 from
    (congr_arg (Poly.send (F i).fires) hz).trans (Poly.send_zero _)))
  obtain ⟨x,hx,hv⟩ := Finset.not_disjoint_iff.mp ((F i).refuses U hh)
  rw [← h.2] at hv
  obtain ⟨j,hj,hx'⟩ := mem_biUnion.mp hv; exact ⟨j,hj,Finset.not_disjoint_iff.mpr ⟨x,(K j).records hx',hx⟩⟩

variable [Fintype ι] [Fintype κ]

theorem coins (U) : (∑ i : Finset ι, Lifted.pack K i U)* (∏ i : κ, ((F i).amount U + 1)) =
    ∑ s : Finset (Latch K F), Lifted.pack (merged K F) s U := by
  let Z := univ.filter (fun s : Finset (Latch K F) => Lifted.gather (merged K F) s U)
  let Y := univ.filter (sailed K F U)
  have hr : ∑ s ∈ Z,Lifted.pack (merged K F) s U=∑ t ∈ Y,cube K F t U := by
    refine sum_bij (fun s _ => unhook K F s) ?_ ?_ ?_ (fun i hi => counted K F U i (mem_filter.mp hi).2)
    · intro s hs; exact mem_filter.mpr ⟨mem_univ _,on K F s U (mem_filter.mp hs).2⟩
    · intro a ha b hb he
      have h := hooked K F a (mem_filter.mp ha).2.1;rw [he, hooked K F b (mem_filter.mp hb).2.1] at h
      exact (Finset.image_inj Subtype.val_injective).mp h.symm
    intro b hb; obtain ⟨q,hq,h⟩ := all_to K F U b (mem_filter.mp hb).2; exact ⟨q,mem_filter.mpr ⟨mem_univ _,hq⟩,h⟩
  have he : ∑ i : Finset (Latch K F), Lifted.pack (merged K F) i U= ∑ s∈ Y, cube K F s U := by
    apply Eq.trans _ hr; symm; refine Finset.sum_subset (subset_univ Z) ?_
    intro i hi hn; exact if_neg (fun H => hn (mem_filter.mpr ⟨hi,H⟩))
  rw [he]
  rw [show (∏ i : κ, ((F i).amount U + 1)) = ∑ s : Finset κ, ∏ i∈s,(F i).amount U by
    simpa using! Fintype.prod_add (fun i => (F i).amount U) (fun _ => 1), Finset.sum_mul_sum]
  have hA (s : Finset ι × Finset κ) : Lifted.pack K s.1 U * (∏ i∈s.2,(F i).amount U) =
      if sailed K F U (s.1.disjSum s.2) then cube K F (s.1.disjSum s.2) U else 0 := by
    rw [Lifted.pack]
    split_ifs with h hp hp'
    · symm; rw [cube]; exact prod_disjSum ..
    · apply Classical.byContradiction; intro hz; apply hp
      refine ⟨by rw [toLeft_disjSum]; exact h,needs K F _ U (by rw [toLeft_disjSum]; exact h) ?_⟩
      rw [cube,prod_disjSum]; exact hz
    · have hv := hp'.1; rw [toLeft_disjSum] at hv; exact False.elim (h hv)
    exact zero_mul ..
  let L := fun s : Finset ι × Finset κ => Lifted.pack K s.1 U * (∏ i∈s.2,(F i).amount U)
  rw [show (∑ s : Finset ι, ∑ t : Finset κ, Lifted.pack K s U * (∏ i∈t,(F i).amount U)) = ∑ s,L s from (Fintype.sum_prod_type L).symm]
  dsimp only [Y]; rw [sum_filter]; exact Fintype.sum_equiv Finset.sumEquiv.symm.toEquiv _ _ hA
end YM.Next.Rank.EntryWord
