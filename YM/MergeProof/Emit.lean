import YM.MergeProof.SwitchCost
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Switch
open Function Set Finset Filter MeasureTheory Marker GridRenewal.Rain
open scoped Topology BigOperators Classical
variable {ι U A V : Type}[Fintype ι] [DecidableEq V]{b : ℝ} {R:Census V}
variable (f : U → Ways ι)(hp : Paid f b)
include hp in
lemma Paid.toPoint (u:U) : Paid (fun _:Unit=>f u) b:=by obtain ⟨a,h,hA,H⟩:=hp; exact ⟨a,h,hA,fun _=>H u⟩ -- include
variable (r:ι→Poly R)
lemma summed (A:Finset U)(c:U→Ways ι)(d:U→ℝ) (h:∀ i∈ A,Paid (fun _:Unit=>c i) (d i)) : sound r (∑ i∈ A,c i)=∑ i∈A, sound r (c i):=by
   induction A using Finset.induction with
   | empty => simp only [Finset.sum_empty]; exact (const_sounds r 0).trans (by simp)
   | insert i s he ih=>
     have hs j hj:= h j (mem_insert_of_mem hj)
     rw [sum_insert he,sum_insert he]; have H:= Paid.sum s _ _ hs; let u:=∑ i∈s,c i
     have hv : (∑ i∈s,(fun _:Unit=>c i)) ()=u:=by rw [Finset.sum_apply]
     obtain ⟨x,hX⟩ := H.works (); rw [hv] at hX; unfold u at hX
     rw [add_sounds r (show Models (c i) _ from ((h i (mem_insert_self ..)).works ()).choose_spec) hX, ih hs]
lemma product (hr:∀ i,r i*r i=0) (A:Finset U)(c:U→Ways ι)(d:U→ℝ)(h:∀ i∈ A,Paid (fun _:Unit=>c i) (d i)): sound r (∏ i∈A,c i)=∏ i∈A,sound r (c i):=by
   induction A using Finset.induction with
   | empty => simp only [Finset.prod_empty]; exact (const_sounds r 1).trans (by simp)
   | insert i s he ih =>
     have hs j hj:= h j (mem_insert_of_mem hj); rw [prod_insert he, prod_insert he]; have H:= Paid.prod s _ _ hs; let u:=∏i∈s,c i
     have hv : (∏ i∈s,(fun _:Unit=>c i)) ()=u:=by rw [Finset.prod_apply]
     obtain ⟨x,hX⟩ := H.works (); rw [hv] at hX; unfold u at hX
     rw [mul_sounds r hr (show Models (c i) _ from ((h i (mem_insert_self ..)).works ()).choose_spec) hX, ih hs]
lemma gather (r:ι→Poly R) (q:Finset ι) (c:ℝ): sound r (click q c)=(↑c:ℂ) • ∏ i∈q,r i:=by rw [sound,(modelClick q c).exact,mapBench]
include hp
lemma Paid.atZero (i:Finset ι)(u:U): jet (f u) ∅= f u 0 i:=by
   obtain ⟨g,h⟩:=hp.works u; rw [h.exact,←h.current _ ⟨le_rfl,zero_le_one⟩]
   unfold value; rw [sum_eq_single ∅]; simp
   · intro j _ hj; rw [zero_pow (ne_of_gt (card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hj))),zero_mul]
   simp
lemma sunset (u:U) (hr:∀ i,(r i).part R.quiet=0) : (sound r (f u)).part R.quiet=f u 0 ∅:=by
   unfold sound; rw [mapScores_apply,Poly.part_sum,sum_eq_single ∅]; rw [hp.atZero,Finset.prod_empty,Poly.part_smul,Poly.one_part,if_pos rfl,mul_one] -- ambiguity
   · intro i _ hi; obtain ⟨j,hj⟩:= Finset.nonempty_iff_ne_empty.mpr hi; rw [Poly.part_smul, ← mul_prod_erase _ _ hj, Poly.quiet_mul,hr,zero_mul,mul_zero]
   simp
end YM.Merge.Switch
