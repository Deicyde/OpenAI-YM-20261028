import YM.MergeProof.Figure

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Extra.Trajectories
variable (K:Box n → Config G n→Poly B)(u : J→Config G n→Poly B) (X:J→Support n)
variable (t:ℝ)(U:Config G n)
abbrev FlowKind (J:Type*) (n: Side):= Box n ⊕ J
def bloom (i:FlowKind J n): Support n:= i.elim Prod.fst X
def bread (i:FlowKind J n): Prop:= i.elim Sure (fun j=>(X j).Nonempty)
def flash (p:Finset (FlowKind J n)): Box n:= (p.biUnion (bloom X),p.toLeft.biUnion Prod.snd)
-- state all flag molecules
structure Sealed (p:Finset (FlowKind J n)): Prop where
    spark: Spark (bloom X) p
    life:p.toLeft.Nonempty
    neat:(p.toLeft:Set (Box n)).PairwiseDisjoint Prod.fst
    bulk:∀ i∈p,bread X i
-- classical decEq may clash. use local.*
variable [DecidableEq J]
abbrev Period := {p:Finset (FlowKind J n)// Sealed X p}
def forst (j:Period X):= flash X j.val
def pork : FlowKind J n→ Config G n→Poly B:= Sum.elim K u
def crow (i:Period X) (U:Config G n):Poly B:= let p:=forst X i; if p.1∩flags t U=p.2 then ∏ j∈i.val,pork K u j U else 0
def paddle (p:Finset (FlowKind J n)):= grid (fun q=>K q U) (flags t U) p.toLeft * ∏ i ∈ p.toRight,u i U
def token (p:Finset (Period X)) := p.biUnion Subtype.val
omit [DecidableEq J] in
lemma moist (p: Period X): Sure (forst X p):=by
   obtain ⟨i,hi⟩:=p.property.life
   have he(i) (hi:i∈p.val.toLeft) : Sure i:= p.property.bulk _ (mem_toLeft.mp hi)
   refine ⟨(he i hi).1.mono (Finset.subset_biUnion_of_mem Prod.snd hi),?_⟩
   intro i hi; obtain ⟨j,hj,hx⟩:= mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨Sum.inl j,mem_toLeft.mp hj,(he j hj).2 hx⟩
lemma net (p:Finset (Period X)): (token X p).toLeft.biUnion Prod.snd=p.biUnion fun i=> (forst X i).2:=by
   ext x; constructor
   · intro hx; obtain ⟨i,hi,hp⟩:= mem_biUnion.mp hx; obtain ⟨j,hj,he⟩:= mem_biUnion.mp (mem_toLeft.mp hi); exact mem_biUnion.mpr ⟨j,hj,mem_biUnion.mpr ⟨i,mem_toLeft.mpr he,hp⟩⟩
   intro hx; obtain ⟨j,hj,he⟩:= mem_biUnion.mp hx; obtain ⟨i,hi,hp⟩:= mem_biUnion.mp he; exact mem_biUnion.mpr ⟨i,mem_toLeft.mpr (mem_biUnion.mpr ⟨j,hj,mem_toLeft.mp hi⟩),hp⟩
lemma separateR (p:Finset (Period X))(H:Packets.selected (forst X) (Pattern (flags t U)) p) : (p:Set _).PairwiseDisjoint (fun j:Period X=> (forst X j).1) ∧ (token X p).toLeft.biUnion Prod.snd= flags t U:=by
   rw [net]; exact (marked_pattern (forst X) _ p (fun i _=> (moist X i).1.mono (moist X i).2)).1 H
lemma lined (p:Finset (Period X))(H:Packets.selected (forst X) (Pattern (flags t U)) p) : Pattern (flags t U) (token X p).toLeft:=by
   obtain ⟨hp,hq⟩:=separateR X t U p H; refine ⟨fun i hi j hj he=> ?_,hq⟩
   obtain ⟨x,hx,hk⟩:= mem_biUnion.mp (mem_toLeft.mp hi); obtain ⟨y,hy,hr⟩:= mem_biUnion.mp (mem_toLeft.mp hj); by_cases h:x=y
   · subst y; exact x.property.neat (mem_toLeft.mpr hk) (mem_toLeft.mpr hr) he
   exact Finset.disjoint_left.mpr fun a ha hA=> disjoint_left.mp (hp hx hy h) (mem_biUnion.mpr ⟨_,hk,ha⟩) (mem_biUnion.mpr ⟨_,hr,hA⟩)
lemma strung (p:Finset (Period X))(H:Packets.selected (forst X) (Pattern (flags t U)) p): paddle K u t U (token X p)= ∏ i∈p,crow K u X t i U:=by
   unfold paddle grid; rw [if_pos (lined X t U p H)]; refine (prod_sum_eq_prod_toLeft_mul_prod_toRight (s:=token X p) (f:=fun i=>pork K u i U)).symm.trans ?_
   have hp := (separateR X t U p H).1
   unfold token; rw [prod_biUnion]; refine prod_congr rfl fun i hi=> ?_; unfold crow; dsimp only; rw [if_pos ?_]; refine Finset.ext (fun j=>?_) -- equality flash flag
   · rw [Finset.mem_inter,← (separateR X t U p H).2,net]; constructor
     · rintro ⟨ht,h⟩; obtain ⟨k,hk,hh⟩:= mem_biUnion.mp h; by_cases hz:k=i; exact (show j∈ (forst X i).2 from hz ▸ (show j∈ (forst X k).2 from hh)); exact False.elim (Finset.disjoint_left.mp (hp hi hk (Ne.symm hz)) ht ((moist X k).2 hh))
     intro hx; exact ⟨(moist X i).2 hx, mem_biUnion.mpr ⟨i,hi,hx⟩⟩
   intro i hi j hj he; apply Finset.disjoint_left.mpr; intro q hq hm; have hv:(bloom X q).Nonempty:= by
     have ht:= i.property.bulk q hq; cases q with
     | inl q=> exact (show Sure q from ht).1.mono (show Sure q from ht).2
     | inr q=> exact ht
   obtain ⟨x,hx⟩:=hv; exact disjoint_left.mp (hp hi hj he) (mem_biUnion.mpr ⟨q,hq,hx⟩) (mem_biUnion.mpr ⟨q,hm,hx⟩)
end YM.MergeProof.Accent
