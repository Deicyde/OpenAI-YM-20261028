import YM.TraceExtension.Cask.Tagged
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker Extra.Trajectories Function
open scoped Classical
variable {V I W:Type*}[DecidableEq V]{R:Type*}[CommRing R] {S T:Finset V}(F:Finset V→R)
def powder (F:Finset V→R)(T:Finset V):= ∑ S∈T.powerset,(-1:R)^((T \ S).card)*F S
lemma powder_of (x:V) (h:x∉S): powder F (insert x S)=powder (fun i=> F (insert x i)-F i) S:=by
    have he(i : Finset V)(hx:i∈S.powerset): x∉i:=fun h'=> h (mem_powerset.mp hx h')
    have ha (i) (hi:i∈S.powerset): insert x S \ i=insert x (S \ i):=by ext j; by_cases hp:j=x; subst j; simp[he i hi]; simp [hp]
    have ht (i : Finset V)(hi:i∈S.powerset): insert x S \ insert x i=S \ i:=by ext j;by_cases hp:j=x; subst j;simp[h]; simp [hp]
    unfold powder; rw[powerset_insert,Finset.sum_union,Finset.sum_image]; swap
    · intro i hi j hj hj'; change insert x i=insert x j at hj'; rw [← erase_insert (he i hi),← erase_insert (he j hj),hj']
    rotate_left
    · refine disjoint_left.mpr fun j hj hb=>?_ ; obtain ⟨v,hv,rfl⟩:=mem_image.mp hb; exact h (mem_powerset.mp hj (mem_insert_self ..))
    rw [← sum_add_distrib]; refine sum_congr rfl fun i hi=>?_ ; rw[ha i hi,ht i hi,card_insert_of_notMem (fun he=> h ((mem_sdiff.mp he).1)),pow_succ]; ring
lemma powder_empty : powder F ∅= F ∅:=by simp [powder]
lemma power_up (S:Finset V): ∑ i∈ S.powerset, powder F i= F S:=by
    induction S using Finset.induction generalizing F with
    | empty => simp[powder_empty]
    | insert i s hi IH=>
      let p (t:Finset V):= F (insert i t)-F t
      have he(t : Finset V)(hx:t∈s.powerset) : i∉t:= fun h=> hi (mem_powerset.mp hx h)
      rw [powerset_insert,sum_union,sum_image];swap
      · intro a ha b hb hm; change insert i a=insert i b at hm; rw[← erase_insert (he a ha),←erase_insert (he b hb),hm]
      rotate_left
      · refine disjoint_left.mpr fun j hj hb=>?_ ; obtain ⟨v,hv,rfl⟩:=mem_image.mp hb; exact hi (mem_powerset.mp hj (mem_insert_self ..))
      rw [sum_congr rfl (f:=fun j=>powder F (insert i j)) (g:=powder p) (fun j hj=> powder_of F i (he j hj)), IH F,IH p]; unfold p; abel
lemma powder_sum (s:Finset I)(T:Finset V)(F:I→ Finset V→R): powder (fun x=>∑ i∈s,F i x) T=∑ i∈s,powder (F i) T:=by simp_rw [powder,mul_sum]; rw[sum_comm]
lemma powder_mono (x:Finset V)(c:R)(S:Finset V): powder (fun i=> if x⊆i then c else 0) S = if x=S then c else 0:=by
    induction S using Finset.induction generalizing x with
    | empty=> by_cases h:x=∅<;>simp[powder,h]
    | insert i s hi IH=>
        rw [powder_of _ _ hi]; by_cases h:i∈x
        · let v:=x.erase i; have ht:x=insert i v:= (insert_erase h).symm; have he:x=insert i s ↔ v=s:= by constructor; intro h; exact (congr_arg (·.erase i) h).trans (erase_insert hi); exact fun h=> h ▸ ht
          rw [if_congr he rfl rfl,← IH v]; unfold powder; refine sum_congr rfl (fun p hp=> ?_)
          have hu : ¬ x⊆p:=fun z=> hi (mem_powerset.mp hp (z h)); have hV:x ⊆ insert i p ↔ v ⊆ p:=by
             constructor
             · intro hh t ht; exact (mem_insert.mp (hh (mem_of_mem_erase ht))).resolve_left (ne_of_mem_erase ht)
             intro h; rw [ht]; exact insert_subset_insert _ h
          simp only[if_neg hu,hV,sub_zero]
        have hz: (fun u:Finset V=> (if x⊆insert i u then c else 0)-(if x⊆u then c else 0))= fun _=>0:=funext fun u=> by
           have hp:x⊆insert i u↔ x⊆u:= ⟨fun he v hv=> (mem_insert.mp (he hv)).resolve_left (fun h'=> h (h' ▸ hv)), fun hv=> hv.trans (subset_insert ..)⟩
           simp only [hp,sub_self]
        rw[hz,if_neg (fun (hx:x=insert i s)=>h (hx.symm ▸ mem_insert_self ..))]; simp[powder]
lemma windF (S:Finset V): ∑ p∈ S.powerset,(-1:R)^p.card*F p= (-1:R)^S.card*powder F S:=by
    unfold powder; rw[mul_sum]; refine sum_congr rfl (fun p hp=>?_)
    have he:(S \ p).card+p.card=S.card:= card_sdiff_add_card_eq_card (mem_powerset.mp hp)
    rw [← mul_assoc,←he,pow_add,mul_right_comm ((-1:R)^_),← pow_add,← two_mul,pow_mul]; simp
end YM.Trace.Cask
