import YM.OPE.Trees.Scene
/-!
# Nested coefficients reorganize into shorter trees
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Nest
open Function Finset Filter
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{L:Register G}{S:Table L} {H:DiffPlan S}(P:Prescription H)(A:Table L)
variable {I:Type}[Fintype I] {s:Arboreal I}{a:Finset I}{i:I}{x:I→ E4}{p:I→L.Token}{w r:Mode H}{D:I→ℕ}{f:I→Mode H}

lemma joins_names (f:I→Mode H)(u:Mode H)(hw:i∈a) : audition P a p (update f i u)=audition P (a.erase i) (update p i (P.letter u)) f:=by
    funext j; by_cases h:j=i; · subst j; simp [audition,hw,update_self]
    simp [audition,h]
lemma cast_pure (hp:i∈ s.middle a) (hw:f∈ s.casting (a.erase i) D w) : f i=w:=(s.casts ..|>.1 hw i).2 (fun hv=> Finset.notMem_erase i a (mem_erase.mp hv).2)
-- dot issue from ..
lemma cast_other {j:I} (he:i≠j) : i∈ s.middle a ↔ i∈ s.middle (a.erase j):= by simp [middle,he]
lemma cast_exchange (h':i∈ s.middle a) (hf:f∈ s.casting (a.erase i) D w)(hr:r∈ bands H (D i)) : update f i r ∈ s.casting a D w:= by
    apply (s.casts ..).2; intro j; by_cases hj:j=i; · subst j; rw [update_self]; simp [h',hr]
    rw [update_of_ne hj,cast_other (show j≠i from hj)]; exact s.casts .. |>.1 hf j
lemma cast_previous (h:f∈s.casting a D w) (he:i∈ s.middle a) : update f i w∈ s.casting (a.erase i) D w:=by
    apply (s.casts ..).2; intro j; by_cases hj:j=i; · subst j; rw [update_self]; simp [middle]
    rw [update_of_ne hj,←cast_other (show j≠i from hj)]; exact (s.casts ..).1 h j

lemma refund (h:s.Border a i)(hp:i∈s.middle a) (x:I→ E4)(p:I→ L.Token)(f:I→Mode H)(u:Mode H) : ensemble P s a x p (update f i u)= coalesce P (s.inputs a i) x p i u * ensemble P s (a.erase i) x (update p i (P.letter u)) f:=by
    unfold ensemble; rw [← mul_prod_erase _ _ (mem_erase.mp hp).2, as_leaf P x h (mem_erase.mp hp).2, update_self]; refine congr_arg _ (prod_congr rfl fun j hj=>?_); unfold eventAt; rw [joins_names P f u (mem_erase.mp hp).2, update_of_ne (mem_erase.mp hj).1]
lemma contracted (h:s.Border a i) (hp:i∈ s.middle a)(x:I→ E4)(p:I→ L.Token)(w:Mode H) (D:I→ℕ): factorization P s a x p w D=∑ u∈ bands H (D i), coalesce P (s.inputs a i) x p i u * factorization P s (s.redact a i) x (update p i (P.letter u)) w D:=by
    unfold factorization; rw [redact_one h]; simp_rw [mul_sum]; symm
    rw [← Finset.sum_product'] -- inspect implicit f
    refine Finset.sum_bij (fun t h => update t.2 i t.1) ?_ ?_ ?_ ?_
    · rintro ⟨u,f⟩ hu; exact cast_exchange hp (mem_product.mp hu).2 (mem_product.mp hu).1
    · rintro ⟨u,f⟩ hu ⟨v,g⟩ hv he
      change update f i u=update g i v at he
      have ht:= congr_fun he i; rw [update_self,update_self] at ht; subst v; congr 1; funext j; by_cases hh:j=i
      · subst j; exact (cast_pure hp (mem_product.mp hu).2).trans (cast_pure hp (mem_product.mp hv).2).symm
      have hb:= congr_fun he j; simpa only [update_of_ne hh] using hb
    · intro f hf; refine ⟨(f i,update f i w),mem_product.mpr ⟨((s.casts ..).1 hf i).1 hp,cast_previous hf hp⟩, by simp⟩
    rintro ⟨u,f⟩ hu; exact (refund P h hp x p f u).symm
-- power normalization for the sum-product at every vertices.
lemma partition (h:s.Active a)(W:I→ℝ) : ∑ x∈a, ∑ i∈ s.kids x, W i= (∑ i∈ s.live a, W i) + ∑ i∈ s.middle a,W i:=by
    let V:= s.live a ∪ s.middle a; have he: Disjoint (s.live a) (s.middle a):= Finset.disjoint_left.mpr (fun i hi h=> (s.live_iff ..|>.mp hi).1 (mem_erase.mp h).2) -- binder i implicit?
    have ht : ∑ x∈ a, ∑ i∈ s.kids x, W i=∑ i∈ V, ∑ x∈ ({s.parent i}:Finset I), W i:=by
       apply Finset.sum_comm' (f:=fun u i=> W i); intro x i; rw [mem_singleton]; constructor
       · rintro ⟨hx,he⟩; obtain ⟨hi,hP⟩:=s.related ..|>.1 he; subst x; refine ⟨rfl,mem_union.mpr ?_⟩; by_cases hh:i∈a; · exact Or.inr (mem_erase.mpr ⟨hi,hh⟩)
         exact Or.inl ((s.live_iff ..).2 ⟨hh,hx⟩)
       rintro ⟨rfl,hP⟩; rcases mem_union.mp hP with hP|hP
       · exact ⟨(s.live_iff ..|>.1 hP).2,(s.related ..).2 ⟨live_other h.main hP,rfl⟩⟩
       exact ⟨h.parent (mem_erase.mp hP).2,s.related ..|>.2 ⟨(mem_erase.mp hP).1,rfl⟩⟩
    rw [ht]; simp_rw [sum_singleton]; exact sum_union he
lemma balance (h:s.Active a) (f:I→ Mode H)(p:I→L.Token)(t:I→ℝ) : ∑ i∈ a,((OPE.sigma (crop (audition P a p f) (s.kids i)):ℝ)-(f i).1)*t i = s.onset t p (s.live a) - (f s.root).1*t s.root - ∑ i∈ s.middle a, (f i).1*s.stepAt t i:= by
    let K:= audition P a p f; let W(i:I):ℝ:= (f i).1; let u:= s.middle a
    let w2(i:I):ℝ:= (K i).1; have he:s.onset t p (s.live a)= ∑ i∈ s.live a,w2 i*t (s.parent i):= sum_congr rfl fun j hj=> by unfold w2 K audition; rw [if_neg (s.live_iff ..|>.1 hj).1];
    have hF : ∑ i∈ u,w2 i*t (s.parent i)=∑ i∈u,W i*t (s.parent i):=sum_congr rfl fun j hj=> by unfold w2 K audition; rw [if_pos (mem_erase.mp hj).2]; rfl;
    have hi (i:I) : (OPE.sigma (crop K (s.kids i)):ℝ)*t i=∑ j∈ s.kids i,w2 j*t (s.parent j):=by rw [sigma_set,Nat.cast_sum,sum_mul]; apply sum_congr rfl; intro j hj; rw [(s.related ..|>.mp hj).2]
    have ht: ∑ i∈ a,W i*t i=W s.root*t s.root+ ∑ i∈ u,W i*t i:= (add_sum_erase _ (fun i=> W i*t i) h.main).symm; have hr: ∑ i∈ u,W i*s.stepAt t i=(∑ i∈ u,W i*t i)- ∑ i∈ u,W i*t (s.parent i):=by unfold stepAt; simp_rw [mul_sub,sum_sub_distrib]
    change ∑ i∈ a,_=(s.onset ..)-W s.root*t s.root- ∑ i∈ u,W i*s.stepAt t i; change ∑ i∈a,((OPE.sigma (crop K (s.kids i)):ℝ)-W i)*t i=_;
    simp_rw [sub_mul,hi]; rw [sum_sub_distrib, (show ∑ i∈ a, ∑ j∈ s.kids i,w2 j*t (s.parent j)=_ from partition h (fun j=>w2 j*t (s.parent j))), hF,← he,ht,hr]; ring
end YM.OPE.Arboreal.Nest
