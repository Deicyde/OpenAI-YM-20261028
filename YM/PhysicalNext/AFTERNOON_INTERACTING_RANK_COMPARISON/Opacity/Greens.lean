import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Pot
/-!
# Mask responsibility on compulsory cores
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display.Sew
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A B : Stores S} {p q : Pilot G S x}
namespace Pot

def bloom (S : StepData c f) (A : Stores S): Support f:= A.costs.biUnion touched

def fields (O : Core S x) := bloom S O.val
lemma transmit (O : Core S x) : (fields O).image S.ratio.parent ⊆ acre O:= by
  intro i hi; obtain ⟨i,hi₁,rfl⟩:= mem_image.mp hi; obtain ⟨j,hj,ht⟩:= mem_biUnion.mp hi₁
  exact halo_subset _ _ (mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨j,hj,mem_image_of_mem _ ht⟩)))
lemma sends_field (e : Wheel c) (O : Core S x): pushed (inflow S e) (fields (hoop S x e O))=fields O:= by
  unfold fields bloom pushed; let F:= shiftFaces e.1 (S.ratio.embed e.2); let Q:= hoop S x e O
  have hh : Q.val.costs = O.val.costs.map F.symm.toEmbedding:= rfl
  refine Eq.trans (migration _ Q.val.costs F _ touched (fun i=>?_)).symm ?_
  · rw [Finset.map_eq_image]; exact Work.H03.touched_send ..
  rw [hh, show ((O.val.costs.map F.symm.toEmbedding).map F.toEmbedding)=O.val.costs by ext i; simp]
lemma owned_fields (A : Stores S) (x : ℝ): (owners A x).biUnion fields=bloom S A:= by
  ext i; constructor
  · intro hi; obtain ⟨j,hj,hp⟩:=mem_biUnion.mp hi; obtain ⟨t,ht,hx⟩:=mem_biUnion.mp hp
    exact mem_biUnion.mpr ⟨t,(pack hj).recognizes.1 ht,hx⟩
  intro hi; obtain ⟨j,hj,h⟩:=mem_biUnion.mp hi
  have hp : Sum.inl j∈(owners A x).biUnion (fun o=>seeds S o.val):= by rw [(owner_eq (A:=A) _|>.1 rfl).2]; exact inl_mem_disjSum.mpr hj
  obtain ⟨a,ha,hj'⟩:=mem_biUnion.mp hp; exact mem_biUnion.mpr ⟨_,ha,mem_biUnion.mpr ⟨_,inl_mem_disjSum.mp hj',h⟩⟩
lemma banner_cap (A : Stores S): (bloom S A).card≤4*A.shares:= by
  have h (i : Cell f): (touched i).card≤4:= Work.E01.touched_card ..
  refine card_biUnion_le.trans ((sum_le_sum fun i _=> h i).trans ?_); simp only [sum_const, smul_eq_mul]
  unfold shares; omega
lemma playsInto (v : Dyed G S) (W : ℝ) (hw : 0<W) (ht : 0<fiery G x S.patch.L) (hv : fiery G x S.patch.L /2 ≤ v.source.p.threshold) (hp : Matched p) (h : v.Playing W p) : flags v.source.p.threshold (v.top p)⊆ (owners p.key x).biUnion fields:= by
  rw [owned_fields]; intro i hi; obtain ⟨j,hj,he⟩:= (flags_spec ..).1 hi
  exact mem_biUnion.mpr ⟨j,Classical.not_not.mp (fun hh=>he.not_ge (((v.participates W hw ht p hp h|>.1.fine j).2 hh).trans hv)),hj⟩

-- not a separate condition to select the owner (compatibility resolves that)

def hoes (v : Dyed G S) (o : Core S x) (p : Pilot G S x):= fields o ∩ flags v.source.p.threshold (v.top p)
lemma hoe_ship (e : Wheel c) (v : Dyed G S) {P : Teller G} (h : P.Funds S v.things) (o : Core S x) (p : Pilot G S x) :
    pushed (inflow S e) (hoes v (hoop S x e o) (spires e p))=hoes v o p:= by
  unfold hoes; rw [Dyed.top_ship v e h p]; unfold pushed; rw [Finset.map_inter]
  exact congr_arg₂ _ (sends_field ..) (dispatched ..).symm

-- mask assignments

def mined (o:Core S x) := univ.filter fun i=> ¬ runUp o.val x i
lemma luck {o : Core S x} {i : Fleck S} (hi : i∈mined o) : ∃ j∈foot S i,j∈o.val.dome (300*radiusB x):= Finset.not_disjoint_iff.mp ((mem_filter.mp hi).2)
lemma deposits (A : Stores S) (x : ℝ) : (owners A x).biUnion mined=univ.filter fun i=> ¬ runUp A x i:= by
  ext i; simp only [mined,mem_biUnion, runUp, mem_filter,mem_univ,true_and, not_disjoint_iff]; constructor
  · rintro ⟨j,hj,v,hv,hx⟩; exact ⟨_,hv,owner_dome A x _ ▸ mem_biUnion.mpr ⟨_,hj,hx⟩⟩
  rintro ⟨j,hj,h⟩; rw [← owner_dome A x] at h; obtain ⟨v,hv,hp⟩ := mem_biUnion.mp h; exact ⟨v,hv,j,hj,hp⟩
lemma entry_point {o : Core S x} {i : Fleck S} (hm : 1 ≤ radiusB x) (hi : i∈mined o) (s) (hs : s∈ foot S i) : Shields (acre o) s (23*radiusB x+17):= by
  obtain ⟨j,hj,hh⟩:=luck hi; apply Shields.shift (o:=j) (t:=23*radiusB x+19) _ ?_
  · intro k hk; apply Aff.facesLocal o.val hh; omega
  exact Nat.add_le_add ((separation_triangle _ (toes S i) _).trans ((Nat.add_le_add ((separation_comm ..).trans_le (strides S i _ hj)) (strides S i _ hs)))) le_rfl |>.trans (by omega)
lemma disjoint_carts (A : Stores S) (x : ℝ) (hm : 1≤radiusB x): (owners A x : Set (Core S x)).PairwiseDisjoint mined:= by
  intro i hi j hj he; refine disjoint_left.mpr fun l ha hb=>?_
  exact disjoint_left.mp (((owner_eq ..).1 rfl).1 hi hj he) (entry_point hm ha _ (footfall S l)|>.center) (entry_point hm hb _ (footfall S l)|>.center)
lemma rotate_mines (e : Wheel c) (o : Core S x): (mined (hoop S x e o)).map (pursuit S e).toEmbedding=mined o:= by
  ext i; obtain ⟨i,rfl⟩:= (pursuit S e).surjective i
  simp only [mem_map_equiv,Equiv.symm_apply_apply,mined,mem_filter,mem_univ,true_and]; exact not_congr (runAt e x i)
end Pot
end YM.PhysicalNext.InteractingRank.Pump
