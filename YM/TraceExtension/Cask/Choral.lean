import YM.TraceExtension.Cask.Boolean
import YM.TraceExtension.Cask.Shore
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker Extra.Trajectories Function
open scoped Classical
variable {L K J V:Type*}[DecidableEq L][DecidableEq K][DecidableEq J][DecidableEq V]{n:Side}[Fintype V]
abbrev Grain (L K J : Type*) := J ⊕ (L⊕ K)
variable (P:Staff V (Grain L K J) n)
structure Roles (x:J→V)(p:K→Box n):Prop where
   field j : P.cast (.inl j)={x j}
   shape i: P.shop i ↔ i.isLeft
   ole i: P.pole i = Sum.elim (fun _=>∅) (Sum.elim (fun _=>∅) (fun k=>(p k).1)) i
   fire i: P.flag i = Sum.elim (fun _=>∅) (Sum.elim (fun _=>∅) (fun k=>(p k).2)) i
   sure k : Sure (p k)
variable (x:J→V)(slotp:K→Box n)(H:Roles P x slotp)
def joinP (s:Finset (Grain L K J)): Finset V := s.toRight.biUnion (fun i=> P.cast (.inr i))
def fetchP (T:Support n)(s:Finset (Grain L K J)): Prop:= Packets.selected x (· = (univ:Finset V)) s.toLeft ∧ joinP P s=univ ∧ Packets.selected slotp (Pattern T) s.toRight.toRight
include H
private lemma colem (q: Finset (Grain L K J)): crew P q=q.toLeft.image x∪joinP P q:=by
   ext j; constructor
   · intro hx; obtain ⟨a,ha,hv⟩:=mem_biUnion.mp hx; cases a with
     | inl a=> exact mem_union_left _ (mem_image.mpr ⟨a,mem_toLeft.mpr ha,(mem_singleton.mp ((H.field a) ▸ hv)).symm⟩)
     | inr a=> exact mem_union_right _ (mem_biUnion.mpr ⟨a,mem_toRight.mpr ha,hv⟩)
   intro hx; rcases mem_union.mp hx with hx|hx
   · obtain ⟨i,hi,rfl⟩:=mem_image.mp hx; exact mem_biUnion.mpr ⟨_,mem_toLeft.mp hi,(H.field i).symm ▸ mem_singleton_self _⟩
   obtain ⟨a,ha,hv⟩:=mem_biUnion.mp hx; exact mem_biUnion.mpr ⟨_,mem_toRight.mp ha,hv⟩
private lemma gore (q: Finset (Grain L K J)): gem P q=q.toRight.toRight.biUnion (fun i=> (slotp i).2):= by
   ext j; constructor
   · intro hx; obtain ⟨k,hk,hj⟩:= mem_biUnion.mp hx; rcases k with k|(k|k)
     · exact False.elim (notMem_empty _ ((H.fire _) ▸ hj))
     · exact False.elim (notMem_empty _ ((H.fire _) ▸ hj))
     exact mem_biUnion.mpr ⟨k,mem_toRight.mpr (mem_toRight.mpr hk), by rw [H.fire] at hj; exact hj⟩
   intro hx; obtain ⟨a,ha,hv⟩:=mem_biUnion.mp hx; exact mem_biUnion.mpr ⟨_,mem_toRight.mp (mem_toRight.mp ha),by rw[H.fire _];exact hv⟩
private lemma pure_ds (q:Finset (Grain L K J)): ((q:Set _).PairwiseDisjoint P.pole) ↔ (q.toRight.toRight:Set _).PairwiseDisjoint (fun i=>(slotp i).1):=by
   constructor
   · intro h i hi j hj hh
     have hu: Sum.inr (Sum.inr i)∈q:= mem_toRight.mp (mem_toRight.mp hi); have hv:= h hu (mem_toRight.mp (mem_toRight.mp (show j∈q.toRight.toRight from hj))) (fun h=> hh (Sum.inr.inj (Sum.inr.inj h)))
     unfold Function.onFun at hv; rw[H.ole,H.ole] at hv; exact hv
   intro h i hi j hj hy; unfold Function.onFun; rw[H.ole,H.ole]; rcases i with i|(i|i) <;> rcases j with j|(j|j) <;> try simp
   exact h (mem_toRight.mpr (mem_toRight.mpr hi)) (mem_toRight.mpr (mem_toRight.mpr hj)) fun ht=> hy (congr_arg (fun j=> Sum.inr (Sum.inr j)) ht)
lemma fetch_eq (q:Finset (Grain L K J))(T:Support n) : fetchP P x slotp T q↔ Woven P q∧crew P q=univ ∧ gem P q=T:=by
   unfold fetchP; rw [marked_pattern ..,gore P x slotp H];swap; exact fun i _=>(H.sure i).1.mono (H.sure i).2
   constructor
   · rintro ⟨⟨hv,hh⟩,hx,hb,he⟩
     change q.toLeft.image x=univ at hv; refine ⟨⟨fun v _=> ?_,fun v _=> ?_,(pure_ds P x slotp H q).2 hb⟩,?_,he⟩
     · obtain ⟨i,hi,hm⟩:= mem_image.mp (show v∈q.toLeft.image x from hv.symm ▸mem_univ v)
       refine ⟨.inl i,⟨mem_toLeft.mp hi,(H.field _).symm ▸ hm.symm ▸ mem_singleton_self _ , (H.shape _).mpr rfl⟩,fun j h=> ?_⟩
       obtain ⟨hj,ht,hy⟩:= h; rcases j with j|j
       · exact congr_arg Sum.inl (hh (mem_toLeft.mpr hj) hi ((mem_singleton.mp ((H.field _) ▸ ht)).symm.trans hm.symm))
       exact False.elim (by have he: false=true:= (H.shape _).1 hy; contradiction)
     · obtain ⟨j,hj,hm⟩:= mem_biUnion.mp (show v∈joinP P q from hx.symm ▸ mem_univ _); exact ⟨.inr j,mem_toRight.mp hj,hm,fun he' => by have hs:false=true:= (H.shape _).1 he'; contradiction⟩
     simp [colem P x slotp H,hx]
   rintro ⟨hp,hc,hf⟩
   have hw(v : V): v∈crew P q:= hc.symm ▸ mem_univ v
   refine ⟨⟨eq_univ_of_forall (fun v=> ?_),fun i hi j hj he=>?_⟩,eq_univ_of_forall (fun v=> ?_), (pure_ds P x slotp H q).1 hp.pole,hf⟩
   · obtain ⟨a,⟨ha,hx,h'⟩,_⟩:=hp.actor v (hw v); rcases a with i|i
     · exact mem_image.mpr ⟨i,mem_toLeft.mpr ha,(mem_singleton.mp ((H.field i) ▸ hx)).symm⟩
     exact False.elim (by have e:false=true:= (H.shape _).mp h'; contradiction)
   · exact Sum.inl.inj ((hp.actor (x j) (hw _)).unique (show _∧_ from ⟨mem_toLeft.mp hi,(show x j∈ P.cast (.inl i) from by rw[H.field _,he]; exact mem_singleton_self _), (H.shape _).2 rfl⟩) (show _∧_ from ⟨mem_toLeft.mp hj, (show x j∈ P.cast (.inl j) from by rw[H.field _];exact mem_singleton_self _), (H.shape _).2 rfl⟩))
   obtain ⟨i,hi,hv,hx⟩:=hp.host v (hw _); rcases i with i|i
   · exact False.elim (hx ((H.shape _).mpr rfl))
   exact mem_biUnion.mpr ⟨i,mem_toRight.mpr hi,hv⟩
end YM.Trace.Cask
