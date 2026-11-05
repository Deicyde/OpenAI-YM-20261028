import YM.Next.MULTISOURCE.Evaluate

/-! Read coefficients of products of individual Wilson factors. -/

set_option autoImplicit false
noncomputable section

namespace YM.Multi
open RG Marker Function Finset
open scoped Topology BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}

omit [Fintype V] in
lemma monomial (f : V → ℂ) (v : Finset V) (T : R.Mode) :
    (∏ i∈v, Poly.send (R.fire i) (f i)).part T = if T.val=v then ∏ i∈v, f i else 0 := by
  have he (v : Finset V) : v ∈ R.choices → ∀ t : R.Mode, t.val=v →
      (∏ i∈v, Poly.send (R.fire i) (f i))=Poly.send t (∏ i∈v,f i) := by
    intro h; induction v using Finset.induction with
    | empty => intro t ht; rw [show t=R.quiet from Subtype.ext ht, prod_empty, prod_empty]; rfl
    | insert i v H ih =>
      intro t ht
      let m : R.Mode := ⟨v,R.down h _ (subset_insert ..)⟩
      rw [prod_insert H, prod_insert H, ih m.property m rfl]
      apply send_prod
      exact ⟨disjoint_left.mpr fun j hj hy => H ((mem_singleton.mp hj) ▸ hy),
        (singleton_union ..).trans ht.symm⟩
  by_cases h : v∈ R.choices
  · rw [he v h ⟨_,h⟩ rfl]; simp only [Poly.part_send, Subtype.ext_iff]
  have hv (v : Finset V) : v∉ R.choices → (∏ i∈v, Poly.send (R.fire i) (f i))=0 := by
    induction v using Finset.induction with
    | empty => exact fun h => False.elim (h R.blank)
    | insert i s hi ih =>
      intro h
      rw [prod_insert hi]
      by_cases hs : s∈R.choices
      · rw [he s hs ⟨_,hs⟩ rfl]
        apply send_noProd
        rintro ⟨z,hz⟩
        apply h
        exact (show insert i s=z.val from (singleton_union i s).symm.trans hz.2) ▸ z.property
      rw [ih hs, mul_zero]
  rw [hv v h, Poly.part_nil, if_neg (show T.val≠v from fun H => h (H ▸ T.property))]

lemma polynomial (f : V → ℂ) (T : R.Mode) :
    (∏ i : V,(1+Poly.send (R.fire i) (f i))).part T=∏ i∈T.val,f i := by
  rw [Finset.prod_one_add, Poly.part_sum, sum_eq_single T.val]
  · simp_rw [monomial]; simp
  · intro b _ hb; simp only [monomial, if_neg (Ne.symm hb)]
  simp

def soloTable {X : Type*} [Zero X] (f : V → X) (q : Hot R) : X :=
  if h : ∃ v, Hot.one R v=q then f h.choose else 0

lemma soloTable_one {X : Type*} [Zero X] (f : V → X) (v : V) : soloTable f (Hot.one R v)=f v := by
  unfold soloTable; split <;> rename_i h
  · rw [(Hot.one_inj ..).mp h.choose_spec]
  exact False.elim (h ⟨_,rfl⟩)

lemma soloTable_not {X : Type*} [Zero X] (f : V → X) (q : Hot R) (h : 2 ≤ q.sites.card) : soloTable f q=0 := by
  unfold soloTable; split
  · rename_i he; obtain ⟨i,hi⟩ := he; simp [← hi] at h
  rfl

lemma solo_sum {X : Type*} (f : V → X → ℂ) (x : X) (R : Census V) :
    lit R (fun i => soloTable f i x) = lambda R fun i => f i x := by
  unfold lit lambda
  let T := Finset.univ.image (Hot.one R)
  symm
  calc
    _ = ∑ i∈ T, Poly.send i.val (soloTable f i x) := by
      rw [sum_image (fun i _ j _ h => (Hot.one_inj ..).mp h)]
      simp_rw [soloTable_one]; rfl
    _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i hi h => by
      have he : ¬∃ v, Hot.one R v=i := by
        simpa only [T,Finset.mem_image, Finset.mem_univ,true_and] using h
      simp [soloTable, he])
end YM.Multi
