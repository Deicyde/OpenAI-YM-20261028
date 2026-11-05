import YM.Next.MULTISOURCE.Boxes

/-!
# Geometry of forced mergers: special shapes with zero or one marker
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Couples
open RG Wilson Lattice Finset Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {n : Side} {V : Type} [DecidableEq V] [Fintype V] (Y : V → Support n)

lemma strike {b} (h : b∈boxes Y) {i} (hi : i ∈ b.toLeft) {j} (hj : j∈b) (he : Sum.inl i ≠ j) :
    ∃ x ∈ b.toRight, ¬ Disjoint (Y x) i.zone := by
  obtain ⟨H,H',-,h⟩ := (owns ..).mp h
  -- moving from this pack has to hit a marker as the first distinct move
  have hl : ∀ v, Ac.chain (span Y) b v (Sum.inl i) → Sum.inl i≠v → ∃ x∈b.toRight, ¬Disjoint (Y x) i.zone := by
    intro v hv hn
    generalize hy : (Sum.inl i : Atom n V)=y at hv
    induction hv with
    | refl => exact False.elim (hn hy)
    | @tail x l h hd ih =>
      subst l
      by_cases he : Sum.inl i=x
      · exact ih he
      cases x with
      | inl k =>
        obtain ⟨h1,h2,y,h3,h4⟩ := hd
        apply False.elim
        have hf : Disjoint i.zone k.zone := H' hi (mem_toLeft.mpr h1) (fun H => he (H ▸ rfl))
        exact Finset.disjoint_left.mp hf h4 h3
      | inr k =>
        obtain ⟨h1,h2,y,h3,h4⟩ := hd
        exact ⟨k,mem_toRight.mpr h1,fun h => Finset.disjoint_left.mp h h3 h4⟩
  exact hl j (h j hj (Sum.inl i) (mem_toLeft.mp hi)) he

lemma all_hit {b} (h : b∈ boxes Y) (hh : b.toRight.Nonempty) :
    ∀ i∈ b.toLeft, ∃ v∈ b.toRight, ¬ Disjoint (Y v) i.zone := by
  obtain ⟨v,hv⟩ := hh
  exact fun i hi => strike Y h hi (mem_toRight.mp hv) (by simp)

omit [DecidableEq V] in
lemma alone (i : Pack n) : ({Sum.inl i}:Recipe n V)∈boxes Y := by
  apply (owns ..).mpr
  have he : ({Sum.inl i}:Recipe n V).toLeft={i} := by ext; simp
  rw [he]; refine ⟨singleton_nonempty _,?_,singleton_nonempty _,?_⟩
  · simp
  intro j hj k hk; rw [mem_singleton.mp hk, mem_singleton.mp hj]; exact .refl

omit [DecidableEq V] in
lemma fused_one (i : Pack n) : fused Y {Sum.inl i}=i := by
  apply Subtype.ext; rw [fused_eq Y (alone Y i)]; apply Prod.ext
  · simp [ground,span]
  simp [tags,show ({Sum.inl i}:Recipe n V).toLeft={i} by ext; simp]

lemma purchase {b i} (h : b ∈ boxes Y) (hv : fused Y b=i) (he : b.toRight=∅) : b={Sum.inl i} := by
  obtain ⟨x,hx⟩ := ((owns ..).mp h).1
  have HH : b={Sum.inl x} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨mem_toLeft.mp hx,fun i hi => ?_⟩
    by_contra hn
    obtain ⟨x,hx,_⟩ := strike Y h hx hi (Ne.symm hn)
    simp [he] at hx
  rw [HH,fused_one] at hv; rwa [← hv]

omit [DecidableEq V] [Fintype V] in
lemma plus_span (i : V) (s : Finset (Pack n)) :
    ground Y (s.disjSum {i}) = Y i ∪ s.biUnion Pack.zone := by
  ext x; simp only [ground, mem_biUnion, mem_union]; constructor
  · rintro ⟨p,hp,H⟩; cases p with
    | inr y =>
      obtain rfl : y=i := mem_singleton.mp (Finset.inr_mem_disjSum.mp hp); left; exact H
    | inl p => exact Or.inr ⟨p, Finset.inl_mem_disjSum.mp hp,H⟩
  · rintro (h|⟨p,hp,h⟩)
    · exact ⟨Sum.inr i,by simp,h⟩
    exact ⟨Sum.inl p,by simp [hp],h⟩

lemma plus_box (i : V) (s : Finset (Pack n)) :
    s.disjSum {i} ∈ boxes Y ↔ s.Nonempty ∧ (s:Set (Pack n)).PairwiseDisjoint Pack.zone ∧
    ∀ j∈s,¬ Disjoint (Y i) j.zone := by
  let a := s.disjSum {i}
  constructor
  · intro h
    obtain ⟨ht,hp,_⟩ := (owns ..).mp h
    refine ⟨by simpa using ht,by simpa using hp,fun j hj => ?_⟩
    obtain ⟨x,hx,H⟩ := strike Y h (show j∈a.toLeft by simpa [a]) (show Sum.inr i∈ a by simp [a]) (by simp)
    obtain rfl : x=i := by simpa using hx
    exact H
  rintro ⟨ht,hp,H⟩
  rw [owns,toLeft_disjSum]; refine ⟨ht,hp,⟨Sum.inr i,by simp⟩,?_⟩
  have he (p) (hh : p∈a) : Ac.chain (span Y) a p (Sum.inr i) := by
    cases p with
    | inr y =>
      obtain rfl : y=i := by simpa [a] using hh
      exact .refl
    | inl k =>
      obtain ⟨z,hz,hz'⟩ := Finset.not_disjoint_iff.mp (H k (by simpa [a] using hh))
      exact .single ⟨hh, by simp [a],z,hz',hz⟩
  intro p hh t hb; exact Relation.ReflTransGen.trans (he p hh) (Ac.swaps (span Y) (he t hb))
end YM.Multi.Couples
