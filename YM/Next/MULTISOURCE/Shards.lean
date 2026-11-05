import YM.Next.MULTISOURCE.Evaluate

/-!
# Partitions at one coefficient. No factorial cost for the number of partitions!
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi
open RG Marker Lattice Function Finset
open scoped Topology BigOperators

variable {V : Type*} [DecidableEq V] {R : Census V}

def rootAt (R : Census V) (i : V) := univ.filter (fun x : Hot R => i∈x.sites)
@[simp] lemma mem_rootAt {x : Hot R} {i : V} : x ∈ rootAt R i ↔ i∈x.sites := by simp [rootAt]

@[simp] lemma chooses (x : R.Mode) (S : (parts R).Mode) : S∈shards R x ↔ unionOf S=x := by simp [shards]
@[simp] lemma hu_chooses (x : Hot R) (S : Hot (parts R)) : S∈blocksOf R x ↔ unionOfHot S=x := by simp [blocksOf]

@[simp] lemma shards_quiet : shards R R.quiet={(parts R).quiet} := by
  ext i; simp only [chooses,mem_singleton]; constructor
  · intro h
    refine Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp ?_)
    intro H
    let x : Hot (parts R) := ⟨i,H⟩
    have he := h ▸ (show (unionOf i).val.Nonempty from (unionOfHot x).property)
    exact not_nonempty_empty he
  rintro rfl; exact unionOf_empty

def contig (v : Hot R) (T : R.Mode) : R.Mode :=
  ⟨T.val \ v.sites, R.down T.property _ (sdiff_subset)⟩

def keepOne (i : V) (T : R.Mode) := (rootAt R i).filter (fun x : Hot R => x.sites ⊆ T.val)

lemma shard_formula (f : Hot R → ℝ) (i : V) (x : R.Mode) (hx : i ∈ x.val) :
    (∑ s∈ shards R x, ∏ b∈s.val,f b)=
      ∑ h ∈ keepOne i x, f h * ∑ s ∈ shards R (contig h x), ∏ b∈s.val,f b := by
  have makes (h : Hot R) (s : (parts R).Mode) (hv : h ∈ keepOne i x)
      (hs : s∈shards R (contig h x)) :
      h ∉ s.val ∧ ∃ t, t∈ shards R x ∧ t.val=insert h s.val := by
    have hH := (chooses _ _).mp hs
    have he := (mem_filter.mp hv).2
    have hg : Poly.merges h.val (unionOf s) x := by
      rw [hH]
      refine ⟨disjoint_sdiff, (union_comm ..).trans (sdiff_union_of_subset he)⟩
    have ht : unionOf ((parts R).fire h)=h.val := unionOf_single _
    obtain ⟨w,hw⟩ := merge_union_inv (show Poly.merges (unionOf ((parts R).fire h)) (unionOf s) x by rw [ht]; exact hg)
    have hi : w.val=insert h s.val := hw.2.symm.trans (singleton_union ..)
    refine ⟨fun H => disjoint_left.mp hw.1 (mem_singleton.mpr rfl) H, w, (chooses ..).mpr ?_,hi⟩
    apply Subtype.ext; rw [← (merge_union hw).2,ht,hg.2]
  let L := (keepOne i x).sigma fun (h : Hot R) => shards R (contig h x)
  have joins (z : Σ _ : Hot R, (parts R).Mode) (hz : z∈L) :
      let a := insert z.1 z.2.val
      ∃ t, t∈ shards R x ∧ t.val=a := (makes _ _ (mem_sigma.mp hz).1 (mem_sigma.mp hz).2).2
  choose j hj hd using joins  -- dependent on hz
  symm
  simp_rw [mul_sum]
  rw [sum_sigma']
  refine sum_bij j hj ?_ ?_ ?_
  · rintro ⟨p,A⟩ hA ⟨q,B⟩ hB h
    have e : insert p A.val=insert q B.val := (hd _ hA).symm.trans ((congrArg Subtype.val h).trans
      (hd _ hB))
    have hv := hd _ hA
    have hp := mem_sigma.mp hA
    have hq := mem_sigma.mp hB
    have he : p=q := by
      by_contra hn
      apply Finset.disjoint_left.mp (parts_wise (j _ hA) (x:=p) (y:=q) ?_ ?_ hn)
        (mem_rootAt.mp (mem_filter.mp hp.1).1) (mem_rootAt.mp (mem_filter.mp hq.1).1)
      · apply mem_coe.mpr; rw [hv]; exact mem_insert_self ..
      apply mem_coe.mpr; rw [h,hd]; exact mem_insert_self ..
    subst q
    congr 1
    apply Subtype.ext
    have hv := congrArg (fun x : Finset _ => x.erase p) e
    rwa [erase_insert (makes p A hp.1 hp.2).1, erase_insert (makes p B hq.1 hq.2).1] at hv
  · intro b hb
    have hU := (chooses ..).mp hb
    obtain ⟨p,hp,hi⟩ := mem_biUnion.mp (show i∈ b.val.biUnion Hot.sites by
      change i∈ (unionOf b).val; rwa [hU])
    let t : (parts R).Mode := ⟨b.val.erase p,(parts R).down b.property _ (erase_subset ..)⟩
    have hh : Poly.merges t ((parts R).fire p) b :=
      ⟨disjoint_left.mpr fun i hi h => notMem_erase p _ ((mem_singleton.mp h) ▸ hi),
        (union_comm ..).trans (by change {p} ∪ _=_; rw [singleton_union]; exact insert_erase hp)⟩
    have hv := merge_union hh
    rw [unionOf_single,hU] at hv
    have he := hv.2
    have hd' : unionOf t=contig p x := by
      apply Subtype.ext
      change _=x.val \ p.sites
      rw [← he]; simp only [Hot.sites,union_sdiff_self,sdiff_eq_self_of_disjoint hv.1]
    have hg : p∈ keepOne i x := mem_filter.mpr ⟨mem_rootAt.mpr hi, he ▸ subset_union_right⟩
    have hB : Sigma.mk (β:=fun _ : Hot R => (parts R).Mode) p t ∈ L := mem_sigma.mpr
      ⟨hg,(chooses ..).mpr hd'⟩
    exact ⟨_,hB,Subtype.ext ((hd _ hB).trans (insert_erase hp))⟩
  rintro ⟨p,b⟩ hb
  rw [hd]
  rw [prod_insert (makes _ _ (mem_sigma.mp hb).1 (mem_sigma.mp hb).2).1]

lemma pays_modes (f : Hot R → ℝ) (h : ∀ i,0≤f i) (hq : ∀ x : V,(∑ i∈rootAt R x, f i) ≤ 1) (T : R.Mode) :
    (∑ s∈shards R T, ∏ i∈s.val,f i) ≤ 1 := by
  by_cases he : T.val.Nonempty
  · obtain ⟨v,hv⟩ := he
    rw [shard_formula f v T hv]
    calc
      _ ≤ ∑ i∈keepOne v T,f i*1 := sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (pays_modes f h hq (contig i T)) (h i)
      _ ≤ _ := by
        simp only [mul_one]; exact (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _ => h i)).trans (hq v)
  rw [show T=R.quiet from Subtype.ext (not_nonempty_iff_eq_empty.mp he), shards_quiet]; simp [Census.quiet]
termination_by T.val.card
decreasing_by
  change (T.val \ i.sites).card < T.val.card
  rw [card_sdiff_of_subset (mem_filter.mp hi).2]
  have h1 := card_pos.mpr i.property
  have he := card_pos.mpr (show T.val.Nonempty from ⟨v,hv⟩)
  exact Nat.sub_lt he h1

lemma pays_parts (f : Hot R → ℝ) (h : ∀ i,0≤f i) (hq : ∀ x : V,(∑ i∈rootAt R x, f i) ≤ 1) (T : Hot R) :
    (∑ H∈blocksOf R T, ∏ i∈ H.sites, f i) ≤ 1 := by
  refine le_trans (le_of_eq (b:=∑ s∈shards R T.val,∏ i∈s.val,f i) ?_) (pays_modes f h hq _)
  refine Finset.sum_bij (fun i _ => i.val) (fun i hi => ?_) (fun i _ j _ h => Subtype.ext h) ?_ (fun _ _ => rfl)
  · exact (chooses ..).mpr (congrArg Subtype.val ((hu_chooses ..).mp hi))
  intro i hi
  have he := (chooses ..).mp hi
  have hh : i.val.Nonempty := by
    by_contra hv
    rw [show i=(parts R).quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hv),unionOf_empty] at he
    exact not_nonempty_empty (he ▸ T.property)
  exact ⟨⟨i,hh⟩,(hu_chooses ..).mpr (Subtype.ext he),rfl⟩

lemma part_size (T : Hot R) (i : Hot (parts R)) (h : i ∈ blocksOf R T) : T.sites.card = ∑ x∈i.sites,x.sites.card := by
  rw [← (hu_chooses ..).mp h]; exact card_biUnion (parts_wise _)
lemma part_cost (T : Hot R) (i : Hot (parts R)) (h : i ∈ blocksOf R T) (w : ℝ) (f : Hot R → ℝ) :
    w^T.sites.card * (∏ j∈i.sites,f j)=∏ j∈i.sites,(w^j.sites.card*f j) := by
  rw [part_size T i h,Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
end YM.Multi
