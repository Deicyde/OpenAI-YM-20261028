import YM.Next.RANK.Flux.Forest

/-!
# Arbitrary marked-root estimate for square-free LOG
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation
open scoped BigOperators Classical

variable {V W ι : Type*} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq ι]

lemma plasma (z : ι → modes V) (X : Finset ι) (c : ι →ℂ) : ∏ j∈X, Poly.send (z j) (c j)=if (X:Set ι).PairwiseDisjoint (fun j=>(z j).val) then Poly.send (scene (X.biUnion fun j=> (z j).val)) (∏ j∈X,c j) else 0:= by
  let f:=fun i=> (z i).val
  induction X using Finset.induction_on with
  | empty=> rw [prod_empty, if_pos (by simp),biUnion_empty,prod_empty];rfl
  | @insert i s hi ih =>
    have ht: (insert i s:Set ι).PairwiseDisjoint f↔ (s:Set ι).PairwiseDisjoint f∧Disjoint (f i) (s.biUnion f):= by
      rw [Set.pairwiseDisjoint_insert_of_notMem (by exact hi)]; simp only [disjoint_biUnion_right]; rfl
    rw [prod_insert hi,biUnion_insert,prod_insert hi,ih]; split
    · rename_i hh
      rw [plate_pair]
      split
      · rename_i hD; rw [if_pos]; congr; rw [coe_insert]; exact ht.mpr ⟨hh,hD⟩
      · rename_i hD; rw [if_neg]; rw [coe_insert]; exact fun h=> hD (ht.mp h).2
    · rename_i hh; rw [mul_zero, if_neg]; rw [coe_insert]; exact fun h=> hh (ht.mp h).1

variable {n : Side} (X : V → Support n)

lemma bleeds (A : Finset V) (v : V) : breeze X A v=
    ∑ s∈(omitX X A v).powerset,(if (s:Set (Finset V)).PairwiseDisjoint id then Poly.send (scene (s.biUnion id)) (∏ i∈s,-majesty X i) else 0):= by
  let Z:= omitX X A v; let P (s : Finset V): veil V:=Poly.send (scene s) (-majesty X s)
  have he : herald X (rests X A v)-herald X (A.erase v)=∑ i∈Z,P i:=by
    rw [throne_up,throne_up,← Finset.sum_sdiff (powerset_mono.mpr (filter_subset _ _ : rests X A v⊆ A.erase v))]
    rw [sub_add_eq_sub_sub_swap]; unfold rests;rw [sub_self,zero_sub,← Finset.sum_neg_distrib]
    apply sum_congr rfl; intro i hi; apply Poly.ext; intro j; rw [Poly.part_neg]; change _=(Poly.send _ _).part _; simp_rw [Poly.part_send]; split_ifs <;> simp
  unfold breeze; rw [he,pass_sum];swap
  · intro i hi; exact asleep (scene i) (omen X hi) _
  rw [prod_congr rfl (g:=fun i=>P i+1) (fun i hi=> solo (scene i) (-majesty X i) (omen X hi)), Finset.prod_add];
  apply sum_congr rfl; intro i hi; rw [Finset.prod_const_one,mul_one]; exact plasma (ι:=Finset V) scene i (fun i=> -majesty X i)

def charges (d : Finset (Finset V)) (s : Finset V) := d.biUnion id=s ∧ (d:Set (Finset V)).PairwiseDisjoint id
lemma pivot {A s : Finset V} (hs : s⊆A) (v : V) (h : v∈s) : majesty X s = ∑ t∈(omitX X A v).powerset,if charges t (s.erase v) then ∏ q∈t, -majesty X q else 0:= by
  have he : (herald X A).part (scene s)= majesty X s:= by rw [throne,if_pos hs]
  rw [← he,assist X (hs h),Poly.part_plus, throne,if_neg (show ¬s⊆A.erase v from fun he=> notMem_erase _ _ (he h)),zero_add,pipe,plate, if_pos (show _ from (show (slot v).val ⊆(scene s).val from singleton_subset_iff.mpr h)),one_mul, bleeds,Poly.part_sum]
  apply sum_congr rfl; intro t _; rw [show (scene s).val\(slot v).val=s.erase v by change s\{v}=_; ext; simp [and_comm]]
  simp only [charges]; split
  · rename_i hh; simp only [Poly.part_send, hh,and_true,same_scene,eq_comm]
  rename_i hh; simp [hh]

lemma majesty_spark {s : Finset V} (h : majesty X s ≠ 0): Ac.Spark X s:= by
  induction s using Finset.strongInduction with
  | H s ih =>
  have hv:s.Nonempty:= nonempty_iff_ne_empty.mpr fun he=> h (he ▸ majesty_zero _)
  refine ⟨hv,fun v hj b hb=> ?_⟩
  rcases eq_or_ne b v with rfl|he; exact .refl
  rw [pivot X (subset_refl _) v hj] at h
  obtain ⟨p,hp,hZ⟩:=Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hZ with HH
  swap; contradiction
  have hz:=mem_erase.mpr ⟨he,hb⟩; rw [← HH.1] at hz
  obtain ⟨d,hd,hh⟩:=mem_biUnion.mp hz
  have hx:=mem_powerset.mp hp hd
  have hu:d⊆s.erase v:=mem_powerset.mp (mem_sdiff.mp hx).1
  obtain ⟨y,hy⟩:=plural X hx; obtain ⟨i,hi,hI⟩:= mem_biUnion.mp (mem_inter.mp hy).1
  have ht: (∏ q∈p, -majesty X q)≠0:=hZ
  have h':d⊂s:= Finset.ssubset_iff_subset_ne.mpr ⟨hu.trans (erase_subset ..),fun h=> notMem_erase _ _ (hu (h.symm ▸ hj))⟩
  have hg:= ih d h' (fun hh=> ht (Finset.prod_eq_zero hd (by simp [hh])))
  exact ReflTransGen.head ⟨hj,(mem_erase.mp (hu hi)).2,y,(mem_inter.mp hy).2,hI⟩ (ReflTransGen.mono (p:= bonds X s) (fun a b h=> ⟨(mem_erase.mp (hu h.1)).2,(mem_erase.mp (hu h.2.1)).2,h.2.2⟩) _ _ (hg.2 i hi b hh))
end YM.Next.Rank.Flux
