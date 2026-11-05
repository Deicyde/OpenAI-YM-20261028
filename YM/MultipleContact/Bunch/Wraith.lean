import YM.MergeProof.Garnish
import YM.MergeProof.North.Blot
import YM.MergeProof.North.Corn
import YM.MergeProof.Sigil
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Fermi
import YM.MultipleContact.Bunch.Farr
import YM.MultipleContact.Bunch.Billow
import YM.MultipleContact.Bunch.Blot
import YM.MultipleContact.Bunch.Corn

/- generalized from YM.MergeProof.North.Wraith to arbitrary arity -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat
open Extra.Multi GridApprox.Nil Ac
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V J : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}
local notation "X"=> Aged V slot
variable (v u:V)(B:Equiv.Perm V)(m:Motion)(x:Site c)
    (K:Box c→ Config G c→Poly (Aged V slot))(ψ:Name V slot→Response G c)(t:ℝ)(U : Config G c)
local notation "Q"=> sky m x
local notation "q"=> puff m x
variable (P:J→Support c)(e:Equiv.Perm J)(he:∀ j,P (e j)=sky m x (P j))
local notation "L"=> Equiv.sumCongr q e
local notation "Q0"=> flags t U
set_option quotPrecheck false
local notation "V0"=>pull m.1 x U
variable (s:Finset (FlowKind J c))
lemma lookout :(s.image L).toLeft=s.toLeft.image q:=by
    ext i; constructor
    · intro hi; obtain ⟨a|b,hv,h⟩:=mem_image.mp (mem_toLeft.mp hi); exact mem_image.mpr ⟨a,mem_toLeft.mpr hv,Sum.inl.inj h⟩; simp at h
    intro hi; obtain ⟨b,hv,rfl⟩:=mem_image.mp hi; exact mem_toLeft.mpr (mem_image_of_mem (L) (mem_toLeft.mp hv))
include he
lemma sealP : Sealed P s↔ Sealed P (s.image L):=by
    let T:= s.image L
    have hc j: bloom P (L j)= (bloom P j).image (turnSites m.1 x):=by cases j; exact shading ..; next j=> exact (he j).trans (shading ..)
    have ht i: i∈ s↔ L i∈T:= (Ribbons.mem_image_of_injective (L) (L).injective).symm -- use explicit
    have hz : Spark (bloom P) s ↔ Spark (bloom P) T := Turn.seam L (turnSites m.1 x) (fun i=> (Turn.display _ _ _).1 (hc i)) ht
    have hv:= lookout m x e s; change T.toLeft=_ at hv
    have hF : s.toLeft.Nonempty↔ T.toLeft.Nonempty:=by rw [hv,image_nonempty]
    have hP : (s.toLeft:Set (Box c)).PairwiseDisjoint Prod.fst↔ (T.toLeft:Set (Box c)).PairwiseDisjoint Prod.fst:=by rw [hv]; exact Twin.dist (R:=J) q s.toLeft (f:=Prod.fst) (f':=Prod.fst) Disjoint Disjoint (fun i _ j _=> (meet_sky m x ..).symm)
    have he(i:FlowKind J c) : bread P i↔ bread P (L i):=by
       cases i
       next i=> change (i.2.Nonempty ∧ i.2⊆ i.1)↔ _ ∧ ((Q) i.2⊆ (Q) i.1); exact and_congr (by change _↔ (Q i.2).Nonempty; rw [shading,image_nonempty]) (by rw [shading,shading,image_subset_image_iff (turnSites m.1 x).injective])
       next i=> change (P i).Nonempty ↔ (P (e i)).Nonempty; rw [he,shading,image_nonempty]
    constructor
    · intro h; refine ⟨hz.1 h.spark,hF.1 h.life,hP.1 h.neat,fun i hi=>?_⟩; obtain ⟨i,hj,rfl⟩:=mem_image.mp hi; exact (he i).mp (h.bulk i hj)
    intro h; exact ⟨hz.2 h.spark,hF.2 h.life,hP.2 h.neat,fun i hi=> (he i).mpr (h.bulk _ ((ht i).1 hi))⟩
lemma ashes : flash P (s.image L)=q (flash P s):=by
    apply Prod.ext
    · change Finset.biUnion _ _= Q _; simp only [shading,image_biUnion]; change _=Finset.image (turnSites m.1 x) (s.biUnion _); rw [biUnion_image]; refine biUnion_congr rfl ?_; intro i hi; cases i
      next i=> exact shading ..
      next i=> exact (he i).trans (shading ..)
    change (s.image L).toLeft.biUnion _= Q (s.toLeft.biUnion _); rw [lookout,image_biUnion,shading,biUnion_image];exact biUnion_congr rfl fun i _=> shading ..
omit he
variable [Fintype J]
lemma rejoins (Z:J→ Config G c→Poly (Aged V slot))(hz:∀ i,Harm v B m (Z i (pull m.1 x U)) (Z (e i) U))(hZ:∀ i,Harm v B m (K i (pull m.1 x U)) (K (puff m x i) U)) (he:∀ j,P (e j)=sky m x (P j))(i:Box c):
       Harm v B m (Accent.closure K Z P t i (pull m.1 x U)) (Accent.closure K Z P t (puff m x i) U):=by
    have hp : Q i.1∩flags t U = Q i.2↔ i.1∩flags t (pull m.1 x U)=i.2:=by
       nth_rw 1 [← Work.H03.flags_send m.1 x]; simp only [shading]; rw [show affine m.1 x=⇑(turnSites m.1 x) from rfl,← Finset.image_inter _ _ (turnSites m.1 x).injective]; exact (Finset.image_injective (turnSites m.1 x).injective).eq_iff
    rw [quarters,quarters];
    let F:= tallyHead K Z P t (pull m.1 x U) i; let G:= tallyHead K Z P t U (q i)
    have hh : ∑ j,G j=∑ j,G ((L).finsetCongr j):=(Equiv.sum_comp ..).symm
    change Harm v B m (∑ j,F j) (∑ j,G j); rw [hh]; refine Harm.seq _ _ _ fun j _=> ?_
    unfold F G tallyHead; rw [show (L).finsetCongr j = j.image L by rw [Equiv.finsetCongr_apply,map_eq_image];rfl];
    have hv: (q i).1∩Q0 = (q i).2 ↔ i.1 ∩ flags t (V0)=i.2:=hp
    simp only [← sealP m x P e he j,ashes m x P e he j,Equiv.apply_eq_iff_eq,hv]; split; swap; exact fun _ _=> (scalar_z _).symm
    rw [prod_image (L).injective.injOn]; apply Harm.prod_; intro j hj; cases j
    next j=> exact hZ j
    next j=> exact hz j
-- row relations only on needed v
omit [Fintype J] in
lemma reborn (hp:B v=u)(he:∀ j:slot,ψ (u,j)= upwards m x (ψ (v,j)))(ht:∀ i,Harm v B m (K i (pull m.1 x U)) (K (puff m x i) U))(i:Box c) :
   Harm v B m (Accent.closure K (conviction ψ (Aged V slot)) Prod.snd t i (pull m.1 x U)) (Accent.closure K (conviction ψ (Aged V slot)) Prod.snd t (puff m x i) U) :=by
    let P:= Equiv.prodCongr (nome (slot:=slot) B) (sky m x); refine rejoins v B m x K t U Prod.snd P _ ?_ ht (fun i=> rfl) _
    rintro ⟨⟨i,b⟩,s⟩; unfold conviction
    let z:=(i,b); change Harm _ _ _ (Poly.send ((X).fire z) (ψ (i,b) s (V0))) (Poly.send ((X).fire (nome (slot:=slot) B z)) (ψ (B i,b) (Q s) U)); let a:=(X).fire z
    rw [← go_one B]; by_cases h:v=i
    · rw [show B i=_ from h ▸ hp,he b,upwards,Equiv.symm_apply_apply, show ψ (i,b)=ψ (v,b) from by rw [h]]; exact Harm.solo _ _
    intro k hk; simp only [Poly.part_send]; have hA:k≠a:=fun e=>h ((which v z).1 (show Focused v a from e ▸ hk)).symm
    simp only [(show k≠(X).fire z from hA),Equiv.apply_eq_iff_eq,↓reduceIte];exact (scalar_z _).symm
end YM.MergeProof.BatchRibbons
