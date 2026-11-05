import YM.MergeProof.Flair
import YM.MergeProof.Stool
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Extra.Trajectories
variable (X:J→Support n)
-- with no leaves
lemma silent_gate (p:Finset (Box n)): Sealed X (p.disjSum ∅) ↔ ∃ i,p={i} ∧ Sure i:=by
   let w(i:Box n):FlowKind J n := .inl i; let R:= p.disjSum (∅:Finset J); have he:R.toLeft=p:= toLeft_disjSum ..; have hf:R.toRight=∅:=toRight_disjSum ..
   constructor
   · intro h;change Sealed X R at h
     obtain ⟨i,hi⟩:= h.life; refine ⟨i,?_, h.bulk (w i) (mem_toLeft.mp hi)⟩
     have hu j (hp:chain (bloom X) R (w i) j): w i=j:=by
        induction hp with
        | refl=>rfl
        | tail _ hk ih=>
          rw [← ih] at hk; obtain ⟨hx,hm,y,hq,hh⟩:=hk; rename_i j' _ -- edit
          first|skip
          cases j' with
          | inl j =>
             by_cases he:i=j; exact congr_arg w he; exact False.elim (Finset.disjoint_left.mp (h.neat hi (mem_toLeft.mpr hm) he) hq hh)
          | inr j=> exact False.elim (Finset.notMem_empty j (hf ▸ mem_toRight.mpr hm))
     ext j; rw [← he,Finset.mem_singleton]; exact ⟨fun hx => (Sum.inl.inj (hu (w j) (h.spark.2 _ (mem_toLeft.mp hi) _ (mem_toLeft.mp hx)))).symm,fun hh=> hh.symm ▸ hi⟩
   rintro ⟨i,hx,h⟩; rw [hx,show disjSum ({i}:Finset _) (∅:Finset J)={w i} from ?_];
   · have he : ({w i}:Finset _).toLeft={i}:=by ext x; unfold w; rw [mem_toLeft,Finset.mem_singleton,Finset.mem_singleton,Sum.inl.injEq]
     refine ⟨⟨Finset.singleton_nonempty _,fun j hj k hk=>?_⟩,he.symm ▸ Finset.singleton_nonempty i,by rw [he]; simp,fun j hj=> (Finset.mem_singleton.mp hj).symm ▸ h⟩
     rw [Finset.mem_singleton.mp hj,Finset.mem_singleton.mp hk]; exact Relation.ReflTransGen.refl
   ext a; cases a<;> simp [w]

lemma street (j:J)(p:Finset (Box n)): Sealed X (p.disjSum {j})↔ Stars (X j) p:=by
   let s:= p.disjSum ({j}:Finset J); let k (i:Box n):FlowKind J n:= .inl i; let x:FlowKind J n:= Sum.inr j
   have h:s.toLeft=p:= toLeft_disjSum ..; have he:s.toRight={j}:= toRight_disjSum ..; have hx:x∈ s:= mem_toRight.mp (he.symm ▸ mem_singleton_self j)
   change Sealed X s↔ _
   constructor
   · intro hp; refine ⟨fun i hi=> hp.bulk (.inl i) (mem_toLeft.mp (h.symm ▸ hi)),h ▸ hp.life,?_,fun i hi=>?_⟩
     · rw [← h]; exact hp.neat
     -- excise x. Pack on leaves force singles.
     let e:= s.erase x; have ht(k':FlowKind J n)(hz:k'∈e):∃ i∈s.toLeft,k'=k i:=by
       obtain ⟨hi,hh⟩:=mem_erase.mp hz; cases k' with
       | inl i=>exact ⟨i,mem_toLeft.mpr hh,rfl⟩
       | inr i=> have hs:i=j:= by have hv:= mem_toRight.mpr hh; rw [he] at hv; exact Finset.mem_singleton.mp hv
                 exact False.elim (hi (congr_arg Sum.inr hs))
     have hk : k i∈e:= mem_erase.mpr ⟨Sum.inl_ne_inr,mem_toLeft.mp (h.symm ▸ hi)⟩
     obtain ⟨a,ha,hb,hc⟩:= excise _ hp.spark hx (k i) hk
     have hu{b c}(hh:chain (bloom X) e b c): b=c:=by
        induction hh with
        | refl=>rfl
        | tail _ hh ih=>
          obtain ⟨i,hi,h1⟩:= ht _ hh.1; obtain ⟨j,hj,h2⟩:= ht _ hh.2.1; rw [h1,h2] at hh; obtain ⟨_,_,y,hb,hc⟩:=hh; have he:i=j:= of_not_not (fun h=> Finset.disjoint_left.mp (hp.neat hi hj h) hb hc); exact ih.trans (h1.trans ((congr_arg k he).trans h2.symm))
     rw [hu hc] at hb; exact Finset.not_disjoint_iff.mpr hb
   intro hp
   have ha(i)(hi:i∈s) : chain (bloom X) s x i:=by
     cases i with
     | inl i=> exact .single ⟨hx,hi,Finset.not_disjoint_iff.mp (hp.meets i (h ▸ mem_toLeft.mpr hi))⟩
     | inr i=>
       have hh:i=j:= by have hv:=mem_toRight.mpr hi; rw [he] at hv; exact Finset.mem_singleton.mp hv
       subst i; exact Relation.ReflTransGen.refl
   refine ⟨⟨⟨x,hx⟩,fun i hi j hj=> Relation.ReflTransGen.trans (swaps _ (ha i hi)) (ha j hj)⟩,h.symm ▸ hp.cash,?_,?_⟩
   · rw [h]; exact hp.safe
   rintro (i|i) hi; exact hp.shines i (h ▸ mem_toLeft.mpr hi)
   have hs:i=j:= by have hv:=mem_toRight.mpr hi; rw [he] at hv; exact Finset.mem_singleton.mp hv
   obtain ⟨u,hu⟩:=hp.cash; obtain ⟨y,hy,-⟩:=Finset.not_disjoint_iff.mp (hp.meets u hu); subst i; exact ⟨y,hy⟩
lemma stepR (j:J)(p:Finset (Box n)): flash X (p.disjSum {j})= cluster (X j) p:=by
   apply Prod.ext
   · ext y; change y∈ Finset.biUnion (p.disjSum {j}) _ ↔ y∈ _∪ p.biUnion Prod.fst
     rw [Finset.mem_biUnion,Finset.mem_union]; constructor
     · rintro ⟨i,hi,ht⟩; rcases i with i|i
       · exact Or.inr (mem_biUnion.mpr ⟨i,(by simpa using hi),ht⟩)
       have hg : i=j:= by simpa using hi
       subst i; exact Or.inl ht
     rintro (hi|hi); exact ⟨.inr j,by simp,hi⟩
     obtain ⟨i,hi,hh⟩:= mem_biUnion.mp hi; exact ⟨.inl i,by simpa using hi,hh⟩
   change (p.disjSum {j}).toLeft.biUnion Prod.snd=p.biUnion Prod.snd; simp
lemma stepL (i:Box n):flash X (({i}:Finset _).disjSum ∅)=i:=by unfold flash; rw [toLeft_disjSum,show disjSum ({i}:Finset _) (∅:Finset J)={Sum.inl i} from (by ext j; rcases j with i|i<;> simp)]; simp [bloom] -- edit
end YM.MergeProof.Accent
