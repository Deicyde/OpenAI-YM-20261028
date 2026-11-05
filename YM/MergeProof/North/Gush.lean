import YM.MergeProof.North.Dew
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Deck
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V] [DecidableEq I][DecidableEq J][Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable (D:Deck V I J G n) (t:ℝ)(U:Config G n)(h:D.Wet t)
open Collide
include h
lemma footprint (i:J): ((D.spill i).1).Nonempty:= (h.sure i).1.mono (h.sure i).2
lemma shade (s:Finset (I⊕J)): D.stain s⊆ D.reach s:=by
   intro i hi; obtain ⟨j,hj,hx⟩:=mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨Sum.inr j,mem_toRight.mp hj,h.old _ ((h.sure j).2 hx)⟩
lemma hold (p:D.Ink): Sure (D.fuse p.val):=by
   obtain ⟨i,hi⟩:=p.property.wet; exact ⟨(h.sure i).1.mono (subset_biUnion_of_mem (fun j=>(D.spill j).2) hi),D.shade _ h _⟩
lemma plume (s:Finset D.Quills) : D.stain (s.biUnion D.glyph)=s.toRight.biUnion fun i=>D.stain i.val:=by
   have hp (i:D.Paper): i.val.toRight=∅:= Finset.not_nonempty_iff_eq_empty.mp (fun hr=> i.property.dry (D.blot _ hr))
   ext i; constructor
   · intro hi; obtain ⟨a,ha,hx⟩:=mem_biUnion.mp hi; obtain ⟨v|v,hv,he⟩:=mem_biUnion.mp (mem_toRight.mp ha)
     · exact (notMem_empty a (hp v ▸ mem_toRight.mpr (show Sum.inr a∈v.val from he))).elim
     exact mem_biUnion.mpr ⟨v,mem_toRight.mpr hv,mem_biUnion.mpr ⟨a,mem_toRight.mpr he,hx⟩⟩
   intro hi; obtain ⟨a,ha,hx⟩:=mem_biUnion.mp hi; obtain ⟨x,hp,hx⟩:=mem_biUnion.mp hx
   exact mem_biUnion.mpr ⟨x,mem_toRight.mpr (mem_biUnion.mpr ⟨_,mem_toRight.mp ha,mem_toRight.mp hp⟩),hx⟩
omit h

-- we propagate Pace predicate irrespective of cost. ensures selected condition, global equality. 
def Pace (s:Finset D.Quills):Prop:= Fits D.quip s ∧ selected (fun i:D.Ink=>D.fuse i.val) (Pattern (flags t U)) s.toRight
include h
lemma repair (s:Finset D.Quills)(hp:D.Pace t U s): D.kiln.slabs (s.biUnion D.glyph)=s.image D.glyph:=by
   have he: (s.image D.glyph).biUnion id=s.biUnion D.glyph:=by rw [image_biUnion]; rfl
   rw [← he]; apply Kiln.undo
   · intro _ hx; obtain ⟨i,-,rfl⟩:= mem_image.mp hx; exact (D.run i).fire
   · intro i hi j hj hz; obtain ⟨a,ha,rfl⟩:= mem_image.mp hi; obtain ⟨b,hb,rfl⟩:=mem_image.mp hj; change Disjoint ((D.glyph a).biUnion _) ((D.glyph b).biUnion _)
     rw [← D.paint,← D.paint]; exact hp.1.1 ha hb fun h=> hz (congr_arg _ h)
   have hh := ((Accent.marked_pattern _ _ _ (fun i _=>(D.hold _ h i).1.mono (D.hold _ h i).2)).mp hp.2).1
   intro i hi j hj hz; obtain ⟨hi,hv⟩:=mem_filter.mp hi; obtain ⟨hj,hx⟩:=mem_filter.mp hj; obtain ⟨a|a,ha,rfl⟩:=mem_image.mp hi
   · exact False.elim (a.property.dry hv)
   obtain ⟨b|b,hb,rfl⟩:=mem_image.mp hj
   · exact False.elim (b.property.dry hx)
   exact hh (mem_toRight.mpr ha) (mem_toRight.mpr hb) (fun h=> hz (congr_arg (fun a:D.Ink=> D.glyph (Sum.inr a)) h))
lemma sheets (s:Finset D.Quills)(hp:D.Pace t U s):
    let p:=s.biUnion D.glyph; selected D.spill (Pattern (flags t U)) p.toRight ∧ (s:Set D.Quills).PairwiseDisjoint D.glyph :=by
   let p:=s.biUnion D.glyph; dsimp only; have he:= D.repair _ _ h _ hp; have hz {i} (hi:i∈s):D.glyph i∈D.kiln.slabs p:=he ▸ mem_image_of_mem D.glyph hi
   have hk := (Accent.marked_pattern _ _ _ (fun i _=> (D.hold _ h i).1.mono (D.hold _ h i).2)).mp hp.2
   refine ⟨(Accent.marked_pattern _ _ _ (fun i _=> D.footprint _ h i)).mpr ⟨fun i hi j hj hn=>?_, (D.plume t h s).trans hk.2⟩,fun i hi j hj hn=> Collide.erases _ p (hz hi) (hz hj) (fun e=>hn (D.tale e))⟩
   obtain ⟨a|a,ha,hI⟩:=mem_biUnion.mp (mem_toRight.mp hi)
   · exact False.elim (a.property.dry (D.blot _ ⟨i,mem_toRight.mpr hI⟩))
   obtain ⟨b|b,hb,hJ⟩:=mem_biUnion.mp (mem_toRight.mp hj)
   · exact False.elim (b.property.dry (D.blot _ ⟨j,mem_toRight.mpr hJ⟩))
   rcases eq_or_ne a b with rfl|e
   · exact a.property.old (mem_toRight.mpr hI) (mem_toRight.mpr hJ) hn
   exact Disjoint.mono (Finset.Subset.trans (h.old (Sum.inr i)) (subset_biUnion_of_mem D.cover (show Sum.inr i∈a.val from hI))) (Finset.Subset.trans (h.old (Sum.inr j)) (subset_biUnion_of_mem D.cover (show Sum.inr j∈b.val from hJ))) (hk.1 (mem_toRight.mpr ha) (mem_toRight.mpr hb) e)
omit h
def bud (p:D.Quills) := ∏ i∈D.glyph p,D.toll i U
def nectar (p:D.Ink) := if D.reach p.val∩ flags t U = D.stain p.val then D.bud U (.inr p) else 0
def sap (p:D.Quills) := Sum.elim (fun i=> D.bud U (.inl i)) (D.nectar t U) p

def value (s:Finset D.Quills):= Ribbons.item D.quip (fun i=>D.fuse i.val) (flags t U) (D.sap t U) s
def fee (s:Finset (I⊕J)):= reap (Ribbons.item D.mode_ D.spill (flags t U) (fun i=> D.toll i U) s)
include h
lemma sweets (s:Finset D.Quills)(hv:D.Pace t U s)(p:D.Quills)(hi:p∈s): D.sap t U p=D.bud U p:=by
   rcases p with b|b; rfl
   change D.nectar t U b=_; unfold nectar; split; rfl
   next he=> symm; by_contra hn; apply he
             have hk := (Accent.marked_pattern _ _ _ (fun i _=> (D.hold _ h i).1.mono (D.hold _ h i).2)).mp hv.2
             ext i; constructor
             · intro hx; obtain ⟨h1,h2⟩:=mem_inter.mp hx; obtain ⟨p,hp,ht⟩:=mem_biUnion.mp (hk.2.symm ▸ h2 : i∈s.toRight.biUnion _)
               by_cases hp':p=b; exact hp' ▸ ht
               exact False.elim ((disjoint_left.mp (hk.1 hp (mem_toRight.mpr hi) hp')) ((D.hold _ h p).2 ht) h1)
             intro hI; refine mem_inter.mpr ⟨D.shade _ h b.val hI,?_⟩; exact hk.2 ▸ mem_biUnion.mpr ⟨b,mem_toRight.mpr hi,hI⟩ -- Eligibility even WITHOUT nonzero
lemma billed (s:Finset D.Quills)(hp:D.Pace t U s): D.fee t U (s.biUnion D.glyph)=D.value t U s:=by
   obtain ⟨ht,hF⟩:=D.sheets t U h s hp
   rw [value,fee,Ribbons.item,if_pos ht,Ribbons.item,if_pos hp.2,prod_biUnion hF];
   have he(p:D.Quills): (∏ i∈D.glyph p,Poly.send (D.mode_ i) (D.toll i U))=Poly.send (D.plank p) (D.bud U p):=tagged_prod _ _ (D.run p).buys _
   simp only [he]; rw [recomp (q:=D.plank) (fun i _=> (D.run i).ready) (D.bud U)]
   exact prod_congr rfl fun i hi=> (congr_arg (Poly.send (D.quip i)) (D.sweets t U h s hp i hi)).symm
end YM.MergeProof.Ribbons.Deck
