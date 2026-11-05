import YM.TraceExtension.Cask.Committee
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
-- Finset book
include H
lemma baler (v:Rain V G)(U:T)(S:Finset V)(h:gazeA C U v univ): gazeA C U v S:= fun i _=>h _ (mem_univ _)
lemma laurels (v:Rain V G)(U:T)(S:Finset V)(h:gazeA C U v univ)(l:L):
    let X:= C.long l
    ∏ i:{s:Finset V// s⊆deer C (C.path l)∧s.Nonempty}, (1+stairC (agency C) S (.inr (.inl ⟨l,i⟩)) (fun p=>lance C p U v)) =
       (Real.exp (X (C.trek S v U)-X U):ℂ):=by
    intro X; let F:= cortex C l U v; let D:= S∩deer C (C.path l); let M:= deer C (C.path l)
    have he: F ∅=0:=by unfold F cortex; rw[H.base]; simp
    have hx:X (C.trek S v U)-X U= F D:=by
        have ht:= H.stitch l (C.trek S v U) (C.trek D v U) (H.view S v (C.path l) U) (by rw[H.mask S U v (baler C H _ _ _ h),H.mask D U v (baler C H _ _ _ h)])
        exact congr_arg (· - X U) ht
    rw [hx,← power_up F D,← sum_erase_add _ _ (mem_powerset.mpr (empty_subset D)),powder_empty,he,add_zero,Real.exp_sum,Complex.ofReal_prod]
    let z:=D.powerset.erase ∅; let f (i:Finset V):ℂ:= Real.exp (powder F i)
    let k (i:{i : Finset V//i⊆M∧ i.Nonempty}):ℂ:= if i.val∈z then f i.val else 1
    have hp(i:{s:Finset V// s⊆deer C (C.path l)∧s.Nonempty}) : 1+stairC (agency C) S (.inr (.inl ⟨l,i⟩)) (fun p=> lance C p U v)= k i:=by
       have hm : i.val∈ z↔ i.val⊆ S:=by
          rw[mem_erase,mem_powerset]; exact ⟨fun hv=> hv.2.trans Finset.inter_subset_left,fun hv=>⟨i.property.2.ne_empty, Finset.subset_inter hv i.property.1⟩⟩
       unfold k stairC; rw [show (agency C).cast _= _ from (show (agency C).cast (.inr (.inl ⟨l,i⟩))=i.val from rfl)]; by_cases ht:i.val∈z
       · rw [if_pos ht,if_pos (hm.1 ht)]; change 1+loft C ⟨l,i⟩ U v=f i.val
         rw [loft,if_pos (baler C H v U i.val h)]; unfold f F; push_cast; ring
       rw [if_neg ht, if_neg (mt hm.mpr ht),add_zero]
    rw [prod_congr rfl (fun i _=>hp i)]; unfold k
    have hy(i:Finset V)(hi:i∈z): i⊆M∧i.Nonempty:=⟨(mem_powerset.mp (mem_of_mem_erase hi)).trans Finset.inter_subset_right,nonempty_iff_ne_empty.mpr (mem_erase.mp hi).1⟩
    rw[← Finset.prod_filter]; refine Finset.prod_bij (fun i _=>i.val) (fun _ hi=> (mem_filter.mp hi).2) (fun _ _ _ _ h=> Subtype.ext h) (fun i hi=>⟨⟨i,hy i hi⟩,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩) (fun i hi=>rfl)
-- owner recovered powder
variable {a b:ℝ}(H':R.activities.Valid R.p a b)
include H'
lemma clinic (v:Rain V G)(U:T)(S:Finset V)(h:gazeA C U v univ)(p:Box n): cram (midland C) (fun i:Axe C=> stairC P! S (.inr (.inr i)) (fun p=> lance C p U v)) p=flore R p (C.trek S v U) :=by
    by_cases he:Sure p
    · let i: BoxF n:= ⟨p,he⟩; let D:= S∩deer C p.1
      let Q:{s: Finset V// s⊆deer C p.1}→ℂ:= fun s=> if s.val⊆ S then powder (skin C p U v) s.val else 0
      have hp (t: {s: Finset V// s⊆deer C p.1}) : stairC P! S (.inr (.inr (⟨i,t⟩:Axe C))) (fun p=>lance C p U v)=Q t:=by
         unfold stairC; change (if t.val ⊆ S then rash C ⟨i,t⟩ U v else 0)= Q t; unfold rash; rw [if_pos (baler C H v U t.val h)]; rfl
      have hx: flore R p (C.trek S v U)= skin C p U v D:= (florid R H' p).1 _ _ (H.view S v p.1 U) (by rw [H.mask _ _ _ (baler C H v U S h), H.mask _ _ _ (baler C H v U D h)])
      rw [hx,← power_up (skin C p U v) D]; unfold cram; rw [tsum_fintype]; let E:= {x:Axe C//midland C x=p}
      let z(t:{s:Finset V//s⊆deer C p.1}):E:= ⟨⟨i,t⟩,rfl⟩
      have hZ : Bijective z:=by
          constructor
          · intro x y hh; exact Subtype.ext (congr_arg (fun q:E=> q.val.2.val) hh)
          rintro ⟨⟨j,t⟩,hz⟩; change j.val=p at hz; obtain rfl:j=i:=Subtype.ext hz; exact ⟨t,rfl⟩
      let m:=Equiv.ofBijective z hZ; rw [← Equiv.sum_comp m]; change (∑ j:{x:Finset V// x⊆deer C p.1}, stairC P! S (.inr (.inr ((⟨i,j⟩:Axe C)))) _ )= _; rw [sum_congr rfl (fun j _=>hp j)]; unfold Q; rw [← sum_filter]; apply sum_bij (fun i _=> i.val)
      · exact fun i hi=> mem_powerset.mpr (Finset.subset_inter (mem_filter.mp hi).2 i.property)
      · exact fun _ _ _ _ h=> Subtype.ext h
      · intro x hx; have hf:= mem_powerset.mp hx; exact ⟨⟨x,hf.trans inter_subset_right⟩, mem_filter.mpr ⟨mem_univ _,hf.trans inter_subset_left⟩,rfl⟩
      intro i hi;rfl
    have hx: flore R p (C.trek S v U)=0:= not_not.mp (fun H=> he ((florid R H' p).2.2.2 _ H).2)
    haveI : IsEmpty {i : Axe C // midland C i=p}:= ⟨fun ⟨v,hv⟩=> he (hv ▸ v.1.property)⟩
    rw[hx]; exact tsum_empty
lemma bright_box (v:Rain V G)(U:T)(S:Finset V)(h:gazeA C U v univ): trump P! (midland C) (flags y! U) (fun i=>lance C i U v) S = ↑(Real.exp (∑ l,C.long l (C.trek S v U) - ∑ l,C.long l U))*(R.activities.gas R.p (C.trek S v U):ℂ):=by
    unfold trump; rw [Fintype.prod_sigma,show (cram _ _)=_ from funext (clinic C H H' v U S h)]; apply congr_arg₂ _
    · simp_rw [laurels C H v U S h]; rw [← sum_sub_distrib,Real.exp_sum,Complex.ofReal_prod]
    rw [← H.mask S U v (baler C H v U S h)]; exact florist R H' _
abbrev markA (i:V)(U:T)(v:b!) := C.marks i U (v i)
abbrev highA (i:V)(U:T)(v:b!) := C.high i U (v i)
lemma arced (U:T)(v:Rain V G)(S:Finset V): brush R C.who (midland C) (lance C) P! U v S=(R.eval (C.trek S v U):ℂ)*tuft (markA C) (highA C) S (C.trek S v U) v :=by
   unfold brush clothW; let F':= fun x:V=> C.high x U (v x)
   simp_rw [show ∀ i, cram C.who ((fun i=>lance C i U v) ∘ Sum.inl) i=F' i from fun i=>(H.finishing i U v).symm]; let V':= C.trek S v U
   unfold tuft
   have hy : ∏ j∈univ \ S,highA C j V' v=∏ j∈univ\ S,F' j:= prod_congr rfl (fun i hi=>H.direct S v U i (mem_sdiff.mp hi).2)
   have hx: ∏ i:V,F' i=(∏ i∈S,C.marks i V' (v i)*(Real.exp (C.fee i U v):ℂ))*∏ i∈ univ \ S,F' i:=by rw [← prod_sdiff (subset_univ S),mul_comm (∏ i∈univ \ S,F' i)]; refine congr_arg₂ (·*·) ?_ rfl; apply prod_congr rfl; intro i hi;exact H.pray S v U i hi
   rw [prod_mul_distrib,← Complex.ofReal_prod,← Real.exp_sum] at hx
   rw [show C.trek S v U= _ from (rfl : C.trek S v U=V'), hy,hx]; by_cases hh:gazeA C U v univ
   · rw [bright_box C H H' v U S hh]; unfold Rep.eval
     rw [Complex.ofReal_mul]; have hp:R.exponent U+(∑ i∈S,C.fee i U v)+(∑ i,C.long i V'-∑ i,C.long i U)=R.exponent V':=by rw [H.splits,H.splits,show C.short V'= _ from H.delta S U v hh]; ring
     rw [← hp,Real.exp_add,Real.exp_add,Complex.ofReal_mul,Complex.ofReal_mul]; unfold V'; change _= _; unfold markA; ring
   have hv: ∏ i:V,F' i=0:= Classical.byContradiction (fun ht=> hh (fun i _=> H.hale _ _ _ (fun h'=>ht (prod_eq_zero (mem_univ i) (show F' i = 0 from h')))))
   have he:∏ i:V,F' i=↑(Real.exp (∑ j∈S,C.fee j U v))*((∏ i∈S,markA C i V' v)*∏ i∈univ \ S,F' i):= hx.trans (by unfold markA; ring)
   have hu: ((∏ i∈S,markA C i V' v)*∏ i∈univ \ S,F' i)=0:= (mul_eq_zero.mp (he.symm.trans hv)).resolve_left (by simp)
   rw [← hx,hv,hu,mul_zero,zero_mul,mul_zero]
lemma meadow : Brant R C.who (midland C) (lance C) (markA C) (highA C) C.trek P!:=⟨H.start,H.tiers,fun i=>based (H.sale i) (fun x:T×Rain V G=> (x.1,x.2 i)) (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd)),fun i=>based (H.heal i) (fun x:T×Rain V G=> (x.1,x.2 i)) (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd)), fun i U u v h=>by simp [highA,markA,h i],arced C H H'⟩
end YM.Trace.Cask
