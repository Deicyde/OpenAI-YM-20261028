import YM.MergeProof.SpreadR
import YM.MergeProof.Vale
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Extra.Trajectories
variable [Fintype J]
variable (K:Box n → Config G n→Poly B)(u : J→Config G n→Poly B) (X:J→Support n)
variable (t:ℝ)(U:Config G n)(p:Box n)
-- flatten token price

def tallyHead (i:Finset (FlowKind J n)):Poly B:= if Sealed X i∧ flash X i=p ∧ p.1∩flags t U=p.2 then ∏ j∈i,pork K u j U else 0
set_option maxHeartbeats 480000 in
lemma quarters : closure K u X t p U=∑ i,tallyHead K u X t U p i:=by
   let f:=tallyHead K u X t U p; let A:= {i:Period X // forst X i=p}
   have he(i:A):f i.val.val=crow K u X t i.val U:=by unfold f tallyHead crow; dsimp only; rw [show flash X i.val.val=p from i.property,i.property]; simp only [i.val.property,true_and]
   let a(i:A):=i.val.val
   have hp : closure K u X t p U=∑' i:A,f (a i) := tsum_congr (fun i=> (he i).symm)
   have hr: ∑' i:A,f (a i)=∑' i,f i:= by
     refine (show Injective a from Subtype.val_injective.comp Subtype.val_injective).tsum_eq (fun i hi=>?_); change f i≠0 at hi; unfold f tallyHead at hi; split at hi
     next ht=> exact ⟨⟨⟨i,ht.1⟩,ht.2.1⟩,rfl⟩
     next=> exact False.elim (hi rfl)
   rw [hp,hr,tsum_fintype]

def briar (θ:Finset J):= ∑ i:Finset (Box n), tallyHead K u X t U p (i.disjSum θ)
lemma roster : closure K u X t p U=∑ i,briar K u X t U p i:=by
   rw [quarters]; let e:= (Finset.sumEquiv (α:=Box n) (β:=J)).toEquiv.symm; rw [← Equiv.sum_comp e,Fintype.sum_prod_type]; exact sum_comm
local notation "T"=> briar K u X t U p
variable (hK: ∀ i,K i U≠0→ i.1∩flags t U=i.2∧Sure i)
include hK
omit [Fintype J] in
lemma baseR : briar K u X t U p ∅=K p U:=by
   unfold briar; rw [sum_eq_single ({p}:Finset (Box n))]
   · unfold tallyHead; rw [silent_gate,stepL]; split
     · rw [show disjSum ({p}:Finset _) (∅:Finset J)={Sum.inl p} by ext i; cases i<;> simp, Finset.prod_singleton]; rfl
     next hh=> exact Eq.symm (not_not.mp (fun h=>hh ⟨⟨p,rfl,(hK _ h).2⟩,rfl,(hK _ h).1⟩))
   · intro b _ hx; unfold tallyHead; rw [silent_gate]; split
     next h=> obtain ⟨⟨j,rfl,hj⟩,he,_⟩:= h; rw [stepL] at he; exact False.elim (hx (congr_arg _ he))
     next=>rfl
   simp
omit hK
variable (A:Activities G n) (hc:∀ i,(K i U).part B.quiet= profile A (fun j=> Complex.ofReal ∘ A.K j) i U)
    (hp:∀ j,(u j U).part B.quiet=0)
include hp
omit [Fintype J] in
lemma abstain (i:Finset J) (h:i.Nonempty): (T i).part B.quiet=0:=by
   unfold briar; rw [Poly.part_sum]; refine Finset.sum_eq_zero (fun j _=>?_); unfold tallyHead; split
   next=> obtain ⟨x,hx⟩:=h; rw [shockProd₀]; exact Finset.prod_eq_zero (show Sum.inr x∈j.disjSum i from by simpa) (hp x)
   next=>rfl
omit [Fintype J] in
lemma freezes (i:Finset J) (h: 2≤ i.card) (j:V): (T i).part (B.fire j)=0:=by
   unfold briar; rw [Poly.part_sum]; refine Finset.sum_eq_zero (fun k _=>?_); unfold tallyHead; split; swap; · rfl
   rw [shockProd]; refine Finset.sum_eq_zero (fun l hl=> ?_); obtain ⟨x,hx,y,hy,hv⟩:= Finset.one_lt_card.mp (by omega : 1 < i.card)
   letI : DecidableEq (Box n ⊕ J) := Classical.decEq _
   have he (r)(hr:r∈i) (hh:Sum.inr r≠ l): Sum.inr r ∈ @Finset.erase _ (Classical.decEq _) (k.disjSum i) l:= mem_erase.mpr ⟨hh, by simpa⟩
   by_cases ht:Sum.inr y=l
   · exact mul_eq_zero.mpr (Or.inr (prod_eq_zero (f:=fun j=>(pork K u j U).part B.quiet) (he x hx (fun hj=>hv (Sum.inr.inj (hj.trans ht.symm)))) (hp x)))
   exact mul_eq_zero.mpr (Or.inr (prod_eq_zero (f:=fun j=>(pork K u j U).part B.quiet) (he y hy ht) (hp y)))
include hc
omit [Fintype J] in
lemma basal (j:J)(i:V) (hs:Summable fun i=>A.K i U): (briar K u X t U p {j}).part (B.fire i)=(u j U).part (B.fire i)*portion A t (X j) p U:=by
   unfold briar; rw [Poly.part_sum,grain _ _ t p U (B:=B) hs, Finset.mul_sum]; apply sum_congr rfl; intro v _
   unfold tallyHead snap reflects; rw [street,stepR]; split
   next h=>rw [prod_sum_eq_prod_toLeft_mul_prod_toRight,toLeft_disjSum,toRight_disjSum,Finset.prod_singleton,shock,shockProd₀]
           change ((∏ j∈v,(K j U).part B.quiet)*_ + _*(u j U).part B.quiet)= _; simp_rw [hc,hp,mul_zero,add_zero]; exact mul_comm ..
   next h=> rw [mul_zero,Poly.part_nil]
include hK
omit hc in
lemma wine : (closure K u X t p U).part B.quiet=(K p U).part B.quiet:=by
   rw [roster,Poly.part_sum,Finset.sum_eq_single ∅,baseR _ _ _ _ _ _ hK]; intro b _ hb; exact abstain K u X t U p hp b (nonempty_iff_ne_empty.mpr hb); simp -- tactic scope
lemma snow (i:V)(hs:Summable fun i=>A.K i U): (closure K u X t p U).part (B.fire i)=(K p U).part (B.fire i)+∑ j,(u j U).part (B.fire i)*portion A t (X j) p U:=by
   rw [roster,Poly.part_sum,← Finset.add_sum_erase _ _ (mem_univ ∅), baseR _ _ _ _ _ _ hK]; congr 1
   let s:= Finset.univ.image fun i:J=> ({i}:Finset J); let f(q:Finset J):= (T q).part (B.fire i)
   change ∑ j∈univ.erase _,f j = _
   have he : s⊆ univ.erase (∅:Finset J):=by intro j hj; obtain ⟨k,_,rfl⟩:=mem_image.mp hj; simp
   rw [← Finset.sum_subset he ?_]; unfold s; rw [sum_image (by intro k _ j _ h;exact Finset.singleton_inj.mp h)]; exact sum_congr rfl (fun j _=> basal K u X t U p A hc hp j i hs)
   intro x hx hh; apply freezes K u X t U p hp x _ i
   have h := Finset.card_pos.mpr (nonempty_iff_ne_empty.mpr (ne_of_mem_erase hx)); have hz: x.card≠ 1:= by intro H; obtain ⟨i,hi⟩:= Finset.card_eq_one.mp H; exact hh (mem_image.mpr ⟨i,mem_univ _,hi.symm⟩) -- indent
   omega
end YM.MergeProof.Accent
