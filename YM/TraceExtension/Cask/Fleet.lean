import YM.TraceExtension.Cask.Muse
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {V L W:Type}[DecidableEq V][DecidableEq L][DecidableEq W]{n:Side}[Fintype V][Fintype L][Fintype W]{G:Gauge}{R:Rep G n}(C:TourC R V L W)(H:AirC C)
local notation "T"=> Config G n
local notation "Y"=> freq V G
local notation "b!"=> Rain V G
local notation "P!"=> agency C
local notation "y!"=> R.p.threshold
-- gaze read is on unshifted U (coded to surround queried edge). track support only ON FOOT.
include H
lemma gene (S:Finset V): MeasurableSet {u:T × Rain V G|gazeA C u.1 u.2 S}:=by
    simp only [gazeA,Set.setOf_forall]; refine MeasurableSet.iInter (fun i :V=> MeasurableSet.iInter fun hi=>?_); exact (show Measurable (fun v:T×Rain V G=> (v.1,v.2 i)) from (Measurable.prodMk measurable_fst ((measurable_pi_apply i).comp measurable_snd))) (H.gaze i)
lemma kin (D:Finset V)(P:Support n)(v:Rain V G): UsesFinal y! (bud C D P) (fun U:T=>gazeA C U v D):=by
    intro U V hu hv; apply propext; unfold gazeA; apply forall_congr'; intro i; refine forall_congr' fun hi=> Iff.of_eq (Work.H03.reads_larger (show C.cap i ⊆ bud C D P from Finset.Subset.trans (Finset.subset_biUnion_of_mem C.cap hi) subset_union_right) (H.bits i (v i)) U V hu hv)
variable {a b:ℝ}(h:R.activities.Valid R.p a b)
include h
lemma spoke (p:LandC C) : Envelope (uncurry (lance C p)):=by
    rcases p with i|(i|i)
    · exact based (H.alignmet i) (fun k:T×Rain V G=> (k.1,k.2 (C.who i))) (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd))
    · have hm(s:Finset V): Envelope (fun k:T×Rain V G=>C.long i.1 (C.trek s k.2 k.1)):=by
        obtain ⟨c,hc⟩:=(H.snow i.1).cost; exact ⟨(H.snow i.1).meas.comp ((H.start s).comp (measurable_snd.prodMk measurable_fst)),c,fun _=>hc _⟩
      have h':Envelope (fun k:T×Rain V G=> C.long i.1 k.1):=by obtain ⟨c,hc⟩:=(H.snow i.1).cost; exact ⟨(H.snow i.1).meas.comp measurable_fst,c,fun _=>hc _⟩
      have hp: Envelope (uncurry (tame C i)):=by
        refine Envelope.sum i.2.val.powerset _ fun j=>?_ ; exact Envelope.mul (Envelope.const _) ((show Envelope (fun k:T×Rain V G=>cortex C i.1 k.1 k.2 j) from by simp_rw [cortex,sub_eq_add_neg]; exact Envelope.add (hm _) h'.neg))
      have hv: Envelope (fun k:T×Rain V G=> if gazeA C k.1 k.2 i.2.val then Real.exp (tame C i k.1 k.2)-1 else 0):=by
        simp_rw [sub_eq_add_neg]; exact Envelope.piece (gene C H _) (Envelope.add hp.exp (Envelope.const _)) (Envelope.const _)
      have ht:= fromR hv; refine Envelope.mk ?_ ?_
      · have he: uncurry (lance C (Sum.inr (Sum.inl i)))=Complex.ofReal ∘ (fun k:T×Rain V G=> if gazeA C k.1 k.2 i.2.val then Real.exp (tame C i k.1 k.2)-1 else 0):=funext fun k=> by change loft C i _ _=Complex.ofReal _; unfold loft; split <;> simp [*, comp_apply]
        exact he.symm ▸ ht.meas
      obtain ⟨c,hc⟩:=ht.cost; refine ⟨c,fun k=> le_trans ?_ (hc k)⟩; change ‖loft C i k.1 k.2‖ ≤ ‖((↑(_ :ℝ)):ℂ)‖; unfold loft;simp_rw [apply_ite Complex.ofReal]; split<;> simp
    let p:=midland C i
    obtain ⟨c,hc⟩:=florW R h; have hf:Envelope (flore R p):=⟨(florid R h p).2.1,c p,(hc.1 p).2⟩
    let f(k:T×Rain V G):ℂ:=powder (skin C p k.1 k.2) i.2.val
    have hy:Envelope f:= envUsum i.2.val.powerset _ (fun s _=> envUmul (constV _) (based hf (fun k:T×Rain V G=>C.trek s k.2 k.1) ((H.start s).comp (measurable_snd.prodMk measurable_fst))))
    change Envelope (fun k:T×Rain V G=> if gazeA C k.1 k.2 _ then f k else 0)
    obtain ⟨c,h,c'⟩:=costNN hy; exact ⟨Measurable.ite (gene C H _) hy.meas measurable_const, c,fun k=> by split; exact c' k; simpa using h⟩
lemma tense (g:Site n→G.El)(i:LandC C)(U:T)(v:Rain V G): lance C i (Lattice.gauge g U) (C.adjust g*v)= lance C i U v:=by
    let q:=Lattice.gauge g U; let V':= C.adjust g*v
    have hp(s:Finset V): gazeA C q V' s↔gazeA C U v s:= forall_congr' fun i=> forall_congr' fun hi=> H.propeller ..
    rcases i with i|(i|i)
    · exact H.artist g U i _
    · change loft C i q V'= loft C i U v; unfold loft; rw [hp,show tame C i q V'= _ from ?_]; unfold tame; congr 1; ext p; unfold cortex; rw [show C.trek p V' q= _ from H.eyes p v U g,(H.hike i.1 g (C.trek p v U)),show C.long i.1 q= _ from H.hike i.1 g U]
    change rash C i q V'= rash C i U v; unfold rash; rw [hp,show skin C (midland C i) q V'= skin C (midland C i) U v from ?_]; funext s; unfold skin; rw [show C.trek s V' q =_ from H.eyes s v U g,(florid R h _).2.2.1 ..]
lemma tells (i:LandC C)(U:T): rule ((agency C).cast i) (lance C i U):=by
    rcases i with i|(i|i)
    · exact fun u v h'=> congr_arg (C.paint i U) (h' _ (mem_singleton_self ..))
    · intro a b hz; unfold lance; change loft C i U a= loft C i U b
      unfold loft; rw [show gazeA C U a i.2.val ↔ gazeA C U b i.2.val from forall_congr' (fun t=> forall_congr' fun ht=> (hz t ht) ▸ Iff.rfl)]
      have ht(x)(hx:x∈i.2.val.powerset): cortex C i.1 U a x=cortex C i.1 U b x:=by unfold cortex; rw[H.drew x a b (fun k hk=>hz k (mem_powerset.mp hx hk))]
      rw [show tame C i U a=tame C i U b from sum_congr rfl (fun t he=>by rw[ht t he])]
    intro a b hz; change rash C i U a=rash C i U b; unfold rash; rw [show gazeA C U a i.2.val ↔ gazeA C U b i.2.val from forall_congr' (fun t=> forall_congr' fun ht=> (hz t ht) ▸ Iff.rfl)]
    have ht(x)(hx:x∈i.2.val.powerset): skin C (midland C i) U a x=skin C (midland C i) U b x:=by unfold skin; rw [H.drew x a b (fun k hk=>hz k (mem_powerset.mp hx hk))]
    rw [show powder (skin C (midland C i) U a) _= powder (skin C (midland C i) U b) i.2.val from sum_congr rfl (fun t he=>by rw[ht t he])]
lemma inlet (p: Finset V)(q:Support n)(s:Finset V) (U V:T)(x:b!)(hV:Agrees (bud C p q) U V)(he: bud C p q∩flags y! U=bud C p q∩flags y! V)(hv:gazeA C U x p)(hp:s⊆p) : Agrees q U V ∧ q∩ flags y! U=q∩flags y! V ∧ Agrees q (C.trek s x U) (C.trek s x V) ∧ q∩flags y! (C.trek s x U)= q∩flags y! (C.trek s x V):=by
   have hx: gazeA C V x p:= Eq.mp (kin C H p q x U V hV he) hv
   have hγ:q⊆bud C p q:= subset_union_left
   have ht: Agrees q U V:= agrees_mono hV (coe_subset.mpr hγ)
   have hy : q∩flags y! U=q∩flags y! V:=by conv_lhs=> rw [← inter_eq_left.mpr hγ,inter_assoc,he,← inter_assoc,inter_eq_left.mpr hγ]
   refine ⟨ht,hy,H.face s x _ _ _ ht,?_ ⟩
   rw[H.mask s U x (fun i hi=>hv i (hp hi)),H.mask s V x (fun i hi=>hx i (hp hi)), hy]
lemma loaded (v:Rain V G)(i:LandC C): UsesFinal y! (P!|>.foot i) (fun U=>lance C i U v):=by
   rcases i with i|(i|i)
   · exact H.strokes i _
   · intro U V hu hv; change loft C i U v=loft C i V v; unfold loft; have h':gazeA C U v i.2.val ↔ gazeA C V v i.2.val:= Iff.of_eq (kin C H _ _ v U V hu hv)
     split_ifs with hx hj <;> first | rfl| tauto | skip
     unfold tame; suffices H : powder (cortex C i.1 U v) i.2.val = powder (cortex C i.1 V v) i.2.val by rw[H]
     refine sum_congr rfl fun k hk=> ?_; obtain ⟨hU,Hv,hq,ht⟩:= inlet C H h i.2.val (C.path i.1) k U V v hu hv hx (mem_powerset.mp hk)
     exact congr_arg (_ * ·) (congr_arg₂ (· - ·) (H.stitch i.1 _ _ hq ht) (H.stitch i.1 U V hU Hv))
   intro U V hu hv; change rash C i U v=rash C i V v; unfold rash; have h':gazeA C U v i.2.val ↔ gazeA C V v i.2.val:= Iff.of_eq (kin C H _ _ v U V hu hv)
   split_ifs with hx hj <;> first | rfl| tauto | skip
   refine sum_congr rfl fun k hk=> ?_; obtain ⟨hU,Hv,hq,ht⟩:= inlet C H h i.2.val (midland C i|>.1) k U V v hu hv hx (mem_powerset.mp hk); exact congr_arg (_ * ·) ((florid R h (midland C i)).1 _ _ hq ht)
lemma kink (U:T)(v:Rain V G)(i:LandC C)(h': lance C i U v≠0): (agency C).pole i∩flags y! U=(agency C).flag i:=by
   rcases i with i|(i|i)
   all_goals try (change ∅∩flags y! U=∅; simp)
   change rash C i U v ≠0 at h'; unfold rash at h'; split at h'; swap; · contradiction
   rename_i he; change _∩_= _; by_contra hq; apply h'; refine sum_eq_zero fun j hj=> ?_
   unfold skin; have hx: flore R (midland C i) (C.trek j v U)=0:= not_not.mp (fun hg=> hq ?_)
   · rw [hx,mul_zero]
   have hν:= ((florid R h _).2.2.2 _ hg).1; rw [H.mask j U v (fun i hi=> he i ((mem_powerset.mp hj) hi))] at hν; exact hν
lemma blank (i:BareP P!) : ∃ (t : BoxF n), i.val=.inr (.inr (patchZ C t)):=by
   rcases i with ⟨i,hi⟩; rcases i with i|(i|⟨v,f⟩)
   · exact False.elim ((singleton_nonempty _).ne_empty hi)
   · exact False.elim (i.2.property.2.ne_empty hi)
   refine ⟨v,congr_arg (fun i: {s:Finset V// s⊆deer C v.val.1}=> Sum.inr (Sum.inr ((⟨v,i⟩:Axe C)))) (Subtype.ext (show f.val=∅ from hi))⟩
lemma clasp (p:BareP P!): (agency C).pole p.val=(agency C).foot p.val:=by
   obtain ⟨t,ht⟩:= blank C H h p; rw [ht]; exact (show t.val.1=t.val.1∪ (∅:Finset V).biUnion C.cap from by rw[biUnion_empty, union_empty])
lemma clearcut (p:Box n)(U:T)(v:Rain V G): cram (wharf P!) (fun i:BareP P!=> lance C i.val U v) p= flore R p U:=by
   by_cases he:Sure p
   · let t: BoxF n:= ⟨p,he⟩; let s:=patchZ C t; let i:BareP P!:=⟨.inr (.inr s),rfl⟩; have ht: wharf P! i=p:=rfl
     rw[expand_eq,tsum_eq_single i]; swap
     · intro j hj; obtain ⟨k,hk⟩:=blank C H h j; have hu : wharf P! j=k.val := by unfold wharf; rw[hk];rfl
       have hx : k.val≠p:= fun he=> hj (Subtype.ext (hk.trans (congr_arg (fun k:BoxF n=> Sum.inr (Sum.inr (patchZ C k))) (Subtype.ext he))))
       exact if_neg (hu ▸ hx)
     rw [if_pos ht]; change rash C s U v= _; unfold rash; change (if gazeA C U v ∅ then powder (skin C p U v) ∅ else 0)= _; rw [if_pos (show gazeA C U v ∅ from by intro k hk; simp at hk),powder_empty,skin,H.base]
   have hx : flore R p U=0:= Classical.byContradiction fun H₁=> he ((florid R h p).2.2.2 _ H₁).2
   rw [hx]; haveI : IsEmpty {i:BareP P!//wharf P! i=p}:= ⟨fun ⟨v,hq⟩=>by obtain ⟨t,ht⟩:= blank C H h v; unfold wharf at hq; rw[ht] at hq; exact he (hq ▸ t.property)⟩
   exact tsum_empty
end YM.Trace.Cask
