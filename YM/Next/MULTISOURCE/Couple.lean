import YM.Next.MULTISOURCE.Boxes

/-!
# Complement reattachment identity with untouched old exclusion
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Couples
open RG Wilson Lattice Finset Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {n : Side} {V : Type} [DecidableEq V] [Fintype V] (Y : V → Support n)
variable {X : Type*} [CommSemiring X]

/-- This weight with its flag check may be assigned to the actual fused entry. -/
def earning (D : Support n) (f : Atom n V → X) (a : Recipe n V) :=
    if ground Y a ∩ D = tags a then ∏ x∈a, f x else 0

def till (D : Support n) (f : Atom n V → X) (i : Pack n) :=
    ∑ j∈ boxes Y with fused Y j = i, earning Y D f j

omit [DecidableEq V] in
set_option maxHeartbeats 600000 in
lemma crossed (f : Atom n V → X) (D : Support n) :
    (∑ B∈accepted Y D, ∏ b∈ B, earning Y D f b) = ∑ b∈intake Y D, ∏ v∈b,f v := by
  symm
  refine Finset.sum_bij (s:=intake Y D) (t:=accepted Y D) (fun i _ => Ac.Parts (span Y) i) (fun i hi => choose_parts Y hi) ?_ ?_ ?_
  · intro i hi j hj he
    exact (Ac.reconstruct (span Y) i).symm.trans (Eq.trans (congrArg (fun b : Finset (Recipe n V) => b.biUnion id) he)
      (Ac.reconstruct (span Y) j))
  · intro i hi
    have H := choose_fuse Y (D:=D) (B:=i) hi
    refine ⟨i.biUnion id,?_,?_⟩
    · exact H
    · exact splits Y i (u:=D) hi
  intro i hi
  let s := Ac.Parts (span Y) i
  have he : (∏ b∈s, ∏ j∈b, f j)=∏ j∈i,f j := by
    simpa only [Ac.reconstruct,id_eq,s] using (prod_biUnion (f:=f) (Ac.different (span Y) i)).symm
  exact he.symm.trans (Finset.prod_congr rfl fun x hx => (if_pos
    (show ground Y x ∩ D=tags x from inventory_at Y s (choose_parts Y hi) hx)).symm)
omit [DecidableEq V] in
lemma tied (f : Atom n V → X) (D : Support n) :
    (∑ S∈Pack.clears D, ∏ i∈S,till Y D f i) = ∑ b∈intake Y D, ∏ v∈b,f v := by
  unfold till
  rw [fiber_gather]
  trans ∑ B∈accepted Y D, ∏ b∈ B, earning Y D f b
  · refine sum_congr ?_ fun _ _ => rfl
    ext; simp only [mem_filter,accepted]
  · exact crossed Y f D

def original (V : Type) [DecidableEq V] [Fintype V] (D : Support n) := univ.filter fun b : Recipe n V =>
    b.toLeft ∈ Pack.clears D

lemma aligned (f : Atom n V → X) (D : Support n) (h : ∀ i,f (.inr i) ≠ 0 → ∃ v∈ Y i, v∈D) :
    (∑ b∈intake Y D, ∏ v∈b,f v)=∑ b∈ original V D,∏ v∈b, f v := by
  have hg (b : Recipe n V) : b∈intake Y D ↔ b.toLeft∈ Pack.clears D ∧ Ac.Parts (span Y) b⊆boxes Y := by
    simp only [intake,mem_filter,mem_univ,true_and]
  have hh (b : Recipe n V) : b∈original V D ↔ b.toLeft∈Pack.clears D := by
    simp only [original,mem_filter,mem_univ,true_and]
  refine Finset.sum_subset (fun b hb => (hh b).mpr ((hg b).mp hb).1) ?_
  intro b he hv
  by_contra hd
  have hu := (hh b).mp he
  apply hv
  apply (hg ..).mpr
  refine ⟨hu,?_⟩
  intro a ha
  obtain ⟨hx,hX⟩ := Ac.lives (span Y) b ha
  have hot i (hi : i∈b) : f i≠0 := fun e => hd (Finset.prod_eq_zero hi e)
  have HE : (b.toLeft : Set (Pack n)).PairwiseDisjoint Pack.zone ∧ b.toLeft.biUnion Pack.flagsAt=D := by
    simpa only [Pack.clears,mem_filter,mem_univ,true_and] using hu
  refine (owns ..).mpr ⟨?_,Set.Pairwise.mono (show a.toLeft ⊆ b.toLeft from
    fun i hi => mem_toLeft.mpr (hx (mem_toLeft.mp hi))) HE.1, hX⟩
  obtain ⟨j,hj⟩ := hX.1
  cases j with
  | inl j => exact ⟨j,mem_toLeft.mpr hj⟩
  | inr j =>
    obtain ⟨v,hv',hV⟩ := h j (hot _ (hx hj))
    obtain ⟨p,hp,hP⟩ := mem_biUnion.mp (show v ∈ b.toLeft.biUnion Pack.flagsAt by rwa [HE.2])
    have he := Ac.contains (span Y) ha (Sum.inr j) hj
    have ht : Sum.inl p∈b := mem_toLeft.mp hp
    refine ⟨p,mem_toLeft.mpr ?_⟩
    rw [← he]
    exact (Ac.bright ..).mpr ⟨ht,Relation.ReflTransGen.single ⟨hx hj,ht,v,hv',p.property.2 hP⟩⟩

omit [DecidableEq V] [Fintype V] in
lemma parts_word (b : Recipe n V) : b.toLeft.disjSum b.toRight=b := by
  ext i; cases i <;> simp

omit [DecidableEq V] [Fintype V] in
lemma split_product (b : Recipe n V) (f : Atom n V → X) :
    (∏ x∈b,f x)=(∏ i∈ b.toLeft,f (.inl i))*∏ i∈ b.toRight,f (.inr i) := by
  nth_rw 1 [← parts_word b]; rw [prod_disjSum]

lemma choices (f : Atom n V → X) (D : Support n) :
    (∑ b∈ original V D, ∏ v∈b,f v)=
      (∑ p∈ Pack.clears D, ∏ i∈p,f (.inl i)) * ∏ i : V,(1+f (.inr i)) := by
  rw [Finset.prod_one_add, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  let F (x : Finset (Pack n) × Finset V) : X := (∏ i∈x.1,f (.inl i)) * ∏ i∈x.2,f (.inr i)
  let q := univ (α:=V)
  change _ = ∑ p∈Pack.clears D, ∑ s∈ q.powerset, F (p,s)
  rw [← Finset.sum_product]
  refine Finset.sum_nbij' (fun b => (b.toLeft,b.toRight)) (fun p => p.1.disjSum p.2) ?_ ?_ ?_ ?_
    (fun i _ => split_product i f)
  · intro i hi; obtain ⟨-,h⟩ := mem_filter.mp hi
    exact mem_product.mpr ⟨h,mem_powerset.mpr (subset_univ _)⟩
  · rintro ⟨s,t⟩ hi
    obtain ⟨h,h'⟩ := mem_product.mp hi
    simp only [original,mem_filter,mem_univ,true_and, toLeft_disjSum]; exact h
  · intro i _; exact parts_word i
  rintro ⟨s,t⟩ h; exact Prod.ext toLeft_disjSum toRight_disjSum

/-- Full exact reassembly at fixed flags. -/
lemma together (f : Atom n V → X) (D : Support n) (h : ∀ i,f (.inr i) ≠ 0 → ∃ v∈Y i,v∈D) :
    (∑ p∈ Pack.clears D,∏ i∈p,till Y D f i) =
      (∑ p∈ Pack.clears D,∏ i∈p,f (.inl i))*∏ i : V,(1+f (.inr i)) := by
  rw [tied,aligned Y f D h,choices]
end YM.Multi.Couples
