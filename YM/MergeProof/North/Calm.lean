import YM.MergeProof.North.Blot
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Twin
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
open Extra.Histories Push Push.Local Motion Equiv
variable {V I J : Type*}[DecidableEq I][DecidableEq J] [DecidableEq V][Fintype V]{G:Gauge}{n:Side}
variable {D:Deck V I J G n}{E:Equiv.Perm I}{F:Equiv.Perm J}{b:Equiv.Perm V}{v u:V}{m:Motion}{x:Site n}(h:Glow D E F v u m x b)
local notation "P!"=> Equiv.sumCongr E F
set_option quotPrecheck false
def Dip (D:Deck V I J G n)(v:V)(s:Finset (I⊕J)) :Prop:=∀ i∈s,Focused v (D.mode_ i)
namespace Glow
include h
variable [Fintype I][Fintype J]
lemma flows {s:Finset (I⊕J)} : Dip D v s ↔ Dip D u (s.image (P!)) :=by
   constructor
   · intro hp i hi; obtain ⟨i,hv,rfl⟩:=mem_image.mp hi; exact (h.lives i).mp (hp i hv)
   intro hp i hi; exact (h.lives i).2 (hp _ (mem_image_of_mem _ hi))
lemma soars (p:Finset (I⊕J) →Prop) (hp:∀ s,Dip D v s→(p s↔ p (s.image (P!)))) :
    ∃ e:Equiv.Perm {s:Finset (I⊕J)//p s},(∀ s,Dip D v s.val ↔ Dip D u (e s).val)∧ ∀ s,Dip D v s.val→(e s).val=s.val.image (P!):=by
   let R:={s:Finset (I⊕J)//p s}; let f:=fun i:R=>Dip D v i.val; let g:=fun i:R=>Dip D u i.val
   let a:{i//f i}→{i//g i}:=fun i=>⟨⟨i.val.val.image (P!), (hp _ i.property).1 i.val.property⟩,h.flows.mp i.property⟩
   have hv:Bijective a:=by
      refine ⟨fun i j he=> Subtype.ext (Subtype.ext (Finset.image_injective (P!).injective (congr_arg (fun i=>i.val.val) he))),fun i=>?_⟩
      obtain ⟨b,hb⟩: (∃ p:Finset (I⊕J),p.image (P!)=i.val.val):=⟨i.val.val.image (P!).symm,(by rw [image_image,show ((⇑(P!)) ∘ ⇑((P!).symm))=id from funext (fun j=>(P!).apply_symm_apply _),image_id])⟩; have ht : Dip D v b:= h.flows.mpr (hb ▸ i.property); exact ⟨⟨⟨b,(hp b ht).2 (hb ▸ i.val.property)⟩,ht⟩,Subtype.ext (Subtype.ext hb)⟩
   obtain ⟨B,hB,hV⟩:= extends_on hv; exact ⟨B,hV,fun s hs=> (congr_arg Subtype.val (hB ⟨s,hs⟩))⟩
lemma tops (i j:D.Quills)(hp:Dip D v (D.glyph i))(he:D.glyph j=(D.glyph i).image (P!))(U:Config G n) : D.reach (D.glyph j)= sky m x (D.reach (D.glyph i))∧ D.quip j=pars b (D.quip i) ∧ D.bud U j= scalar m (D.bud (pull m.1 x U) i) :=by
   refine ⟨?_,?_,?_⟩
   · unfold Deck.reach; rw [he,image_biUnion,shading,biUnion_image]; exact biUnion_congr rfl (fun i hi=>(h.paint i (hp i hi)).2.1.trans (shading ..))
   · rw [Deck.quip,Deck.quip, ← recall]; refine congr_arg Ribbon.span ?_
     rw [← show unionTag _ _ ((h.license hp).mp (D.run i).buys)=drum b (D.plank i) from h.enters hp _]; apply Subtype.ext; change (D.glyph j).biUnion _=_; rw [he]; rfl
   unfold Deck.bud; rw [he,prod_image (P!).injective.injOn]; have hs(q:Finset (I⊕J))(f:I⊕J→ℂ):scalar m (∏ i∈q,f i)=∏ i∈q,scalar m (f i):=by unfold scalar; split_ifs; exact star_prod ..;rfl
   rw [hs];exact prod_congr rfl fun b hb=> congr_fun (h.paint _ (hp b hb)).2.2 U
lemma spat (i j:D.Ink)(hp:Dip D v i.val)(he:j.val=i.val.image (P!))(t : ℝ)(U:Config G n) : D.fuse j.val=puff m x (D.fuse i.val)∧ D.quip (.inr j)=pars b (D.quip (.inr i)) ∧ D.nectar t U j=scalar m (D.nectar t (pull m.1 x U) i):=by
   obtain ⟨hz,hI,hx⟩:= h.tops (Sum.inr i) (Sum.inr j) hp he U
   change D.reach j.val= sky m x (D.reach i.val) at hz
   have ha:D.stain j.val=sky m x (D.stain i.val):=by
      unfold Deck.stain; rw [he,shores,image_biUnion,shading,biUnion_image]; exact biUnion_congr rfl (fun v hv=> (show (D.spill (F v)).2=_ from congr_arg Prod.snd (h.flood v (hp _ (mem_toRight.mp hv)))).trans (shading ..))
   refine ⟨Prod.ext hz ha,hI,?_⟩; unfold Deck.nectar; rw [ha,hz];
   have hh : sky m x (D.reach i.val)∩flags t U=sky m x (D.stain i.val)↔ D.reach i.val∩flags t (pull m.1 x U)= D.stain i.val:=by
      nth_rw 1 [← Work.H03.flags_send m.1 x]; simp only [shading]; rw [show affine m.1 x= ⇑(turnSites m.1 x) from rfl,← Finset.image_inter _ _ (turnSites m.1 x).injective]; exact (Finset.image_injective (turnSites m.1 x).injective).eq_iff
   simp only [hh]; split; exact hx; exact (scalar_z _).symm
end Glow
end YM.MergeProof.Ribbons.Twin
