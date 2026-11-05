import YM.TraceExtension.Cask.Tidal
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker Extra.Trajectories Function Push
open scoped Classical
variable {I V:Type*}[DecidableEq I][DecidableEq V]{n:Side}[Fintype V]
variable (P:Staff V I n) {q:Finset I} (T:Support n)(L:Finset I→ℂ)
abbrev BareP := {i:I// P.cast i=∅}
abbrev TintP := {b:Arch P // (crew P b.val).Nonempty}
abbrev TideP := {b:Arch P // ¬(crew P b.val).Nonempty}
variable (H:∀ i:BareP P,P.pole i.val=P.foot i.val)
lemma crew_silent (i:BareP P): crew P ({i.val}:Finset I)=∅:=by simp [crew,i.property]
include H
lemma heavyA (h:Boat P q)(hx:¬(crew P q).Nonempty)(i:I)(hi:i∈q): q={i}:=by
    have ht:crew P q=∅:= Finset.not_nonempty_iff_eq_empty.mp hx
    have hp(j)(hj:j∈q):P.pole j=P.foot j:= H ⟨j,eq_empty_iff_forall_notMem.mpr (fun v hv=> hx ⟨v,mem_biUnion.mpr ⟨j,hj,hv⟩⟩)⟩
    apply Subset.antisymm _ (singleton_subset_iff.mpr hi); intro j hj; have hr:=h.force.2 i hi j hj
    induction hr with
    | refl=> exact mem_singleton_self _
    | tail hu hv ih=>
       rename_i a b
       obtain ⟨H₀,H₁,H₂⟩:= hv; obtain ⟨p,hp',hq⟩:=H₂
       obtain rfl:a=b:= of_not_not fun hz=> disjoint_left.mp (h.sound.pole H₀ H₁ hz) ((hp a H₀).symm ▸ hp') ((hp b H₁).symm ▸ hq); exact ih H₀
-- bare pole = f required for rewriting.Pinned footprint stock
lemma pond (i:BareP P): Boat P {i.val}:=by
   let q:Finset I := {i.val}; have hx : crew P q=∅:=crew_silent P i; have hp(v):v∉crew P q:=by rw[hx]; exact notMem_empty _
   obtain ⟨x,hx⟩:= fest P i.val; rw [← H i] at hx
   refine ⟨⟨fun v hv=>(hp v hv).elim,fun v hv=>(hp v hv).elim,by simp⟩,⟨singleton_nonempty _,fun a ha b hb=> ?_⟩,(P.needs i.val ⟨_,hx⟩).mono (Finset.subset_biUnion_of_mem P.flag (mem_singleton_self _))⟩
   rw [mem_singleton.mp ha,mem_singleton.mp hb]; exact .refl
abbrev earP (i:BareP P): TideP P:=⟨⟨{i.val},pond P H i⟩,by rw [not_nonempty_iff_eq_empty]; exact crew_silent P i⟩
private lemma seaG : Bijective (earP P H):=by
    refine ⟨fun i j hij=> Subtype.ext (Finset.singleton_injective (congr_arg (fun p:TideP P=> p.val.val) hij)),fun j=>?_⟩
    obtain ⟨i,hi⟩:=j.val.property.force.1; have hp:= heavyA P H j.val.property j.property i hi
    refine ⟨⟨i,eq_empty_iff_forall_notMem.mpr (fun v hv=>j.property ⟨v,mem_biUnion.mpr ⟨i,hi,hv⟩⟩)⟩,Subtype.ext (Subtype.ext hp.symm)⟩
abbrev wharf (k:BareP P): Box n:=(P.pole k.val,P.flag k.val)
lemma pierP (k:BareP P): Pier P (earP P H k).val=wharf P k:=Prod.ext (by simp [hill,H k]) (by simp [gem])
lemma cost_bare (k:BareP P)(hp:∀ q,L q ≠0→∀ i∈q,P.pole i∩T=P.flag i): red P L T {k.val}= L {k.val}:=by
    unfold red; by_cases he: L {k.val}=0
    · simp [he]
    rw[if_pos]; have ht:= hp _ he _ (mem_singleton_self _); rw [H] at ht
    refine ⟨fun r hr=>?_, by simpa [gem,hill] using ht⟩
    obtain ⟨i,hi,Hg⟩:= mem_image.mp hr; subst r; rw[show burst (sector P) {k.val} i={k.val} from ?_,hill,singleton_biUnion]; rw [Finset.disjoint_iff_inter_eq_empty,ht]
    · have hz:= (pond P H k).wet; simp only [gem,singleton_biUnion] at hz; exact hz.ne_empty
    obtain rfl:= mem_singleton.mp hi; apply Finset.Subset.antisymm; exact fun j hj=> ((bright ..).1 hj).1; exact singleton_subset_iff.mpr ((bright ..).2 ⟨mem_singleton_self _,.refl⟩)
variable [Fintype I]
omit H
-- op cargo flagged tags
abbrev buoyT (p:Box n): Poly (Twin V):= cram (fun i:TintP P=> Pier P i.val) (fun i:TintP P=> shipP (crew P i.val.val) (red P L T i.val.val)) p
lemma seal_add (s:Finset I) (F:I→ℂ): (∑ i∈s,Poly.bead (Twin V) (F i))=Poly.bead (Twin V) (∑ i∈s,F i):=by induction s using Finset.induction with
 | empty=> simp [Poly.bead]
 | insert i s hi H=> rw [sum_insert hi,sum_insert hi,H]; exact (send_add ..).symm
include H
lemma soft_p (hp:∀ q,L q ≠0→∀ i∈q,P.pole i∩T=P.flag i)(p:Box n):
    cargo P T L p= Poly.bead (Twin V) (cram (wharf P) (fun i=> L {i.val}) p)+buoyT P T L p:=by
    let f:=fun i:Arch P=> shipP (crew P i.val) (red P L T i.val)
    let g:=fun i:Arch P=> if Pier P i=p then f i else 0
    have hr(i:BareP P): g (earP P H i).val= Poly.bead (Twin V) (if wharf P i=p then L {i.val} else 0):=by
        unfold g;rw [pierP]; split_ifs
        · unfold f; rw [show red P L T (earP P H i).val.val =_ from cost_bare P T L H i hp, shipP, show crew P (earP P H i).val.val =∅ from crew_silent P i]; exact congr_arg (fun w=> Poly.send w _) (Subtype.ext (by simp [spanZ,Census.quiet]))
        simp [Poly.bead]
    let e:=Equiv.ofBijective (earP P H) (seaG P H)
    let t := fun i:Arch P=> (crew P i.val).Nonempty
    have hx:∑ i,g i=(∑ i:TideP P,g i.val)+∑ i:TintP P,g i.val:=by
       rw [add_comm]; exact Eq.symm (Fintype.sum_subtype_add_sum_subtype (p:=t) g)
    have hy :∑ i:TideP P,g i.val=(Poly.bead (Twin V) (cram (wharf P) (fun i=> L {i.val}) p)):=by
       rw [expand_eq,tsum_fintype,← seal_add]; exact Fintype.sum_equiv e.symm _ _ (fun j=> show _ from ((show g j.val=g (earP P H (e.symm j)).val from congr_arg (fun k:TideP P=> g k.val) (e.apply_symm_apply j).symm).trans (hr (e.symm j))))
    unfold cargo buoyT; rw[expand_eq,tsum_fintype]; rw [show _=_ from hx,hy]; congr 1; rw [expand_eq,tsum_fintype]
end YM.Trace.Cask
