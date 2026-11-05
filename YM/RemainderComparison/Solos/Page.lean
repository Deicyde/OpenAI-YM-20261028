import YM.RemainderComparison.Serif.Price
/-!
# Holding tests

For a finite set of slot names, each testing its own, potentially
infinite-dimensional real normed input, linearity datum along labelled
addresses without taking ANY finite-dimensional comparison constants.
Off-mask values of analytic manipulators on the compact gauge group needn't
be linear in those parameters (integral away from specified masks/closed
boundaries may diverge); we will insist on neighborhoods honoring all unit
choices simultaneously, and choose off-domain continuation explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Solos
open Finset Set Filter Function MeasureTheory Push Push.AbsoluteSums
open Mosaic Marker
open scoped Topology BigOperators
variable {θ : Type} (R : θ→Type*) [∀ i, NormedAddCommGroup (R i)] [∀ i,NormedSpace ℝ (R i)]
abbrev Scope (i:θ) := {x:R i // ‖x‖≤1}
abbrev Audited := ∀ i, Scope R i
namespace Scope
variable (i:θ)
def anchor : Scope R i := ⟨0,by simp⟩
end Scope
instance : Nonempty (Audited R):=⟨Scope.anchor R⟩
variable {R}
open scoped Classical
-- classical instance for update
structure LinearP (P : Finset θ)(f:Audited R→ ℝ) : Prop where
   frame : ∀ a b,(∀ i∈P,a i=b i)→ f a=f b
   draws (i:θ): i∈P→ ∀ (a:Audited R)(b c d: Scope R i)(z y:ℝ), b.val=z • c.val+y • d.val → f (Function.update a i b)=z*f (Function.update a i c)+y*f (Function.update a i d)
variable {p q:Finset θ}{f g:Audited R→ℝ}{x v:ℝ}
lemma LinearP.always (h : LinearP p f){i:θ}(hi:i ∉ p)(a:Audited R)(b:Scope R i) : f (Function.update a i b)=f a:= h.frame _ _ fun j hj=> Function.update_of_ne (fun (h:j=i)=> hi (h ▸ hj)) _ _
lemma LinearP.buoy (x:ℝ): LinearP ∅ (fun _: Audited R=>x):= ⟨fun _ _ _=> rfl,fun j hi=> by simp at hi⟩
lemma LinearP.nil (p:Finset θ): LinearP p (fun _: Audited R=>0):= ⟨fun _ _ _=> rfl,fun i _ a c' b c x y e=>by simp⟩
lemma LinearP.tune (h:LinearP ∅ f)(a b): f a=f b:= h.frame _ _ (by simp)
lemma LinearP.plus (h:LinearP p f)(hh:LinearP p g): LinearP p (fun i=>f i+g i):=by
   refine ⟨fun i j hi=> congr_arg₂ _ (h.frame i j hi) (hh.frame i j hi), fun i hi a d b c x y hB=>?_⟩
   rw [h.draws i hi a d b c x y hB,hh.draws i hi a d b c x y hB]; ring
lemma LinearP.grape (h:LinearP p f)(hh:LinearP q g) (hp: Disjoint p q) : LinearP (p∪q) (fun x=>f x*g x):=by
   refine ⟨fun i j hi=> congr_arg₂ _ (h.frame i j (fun v hv=> hi v (Finset.mem_union_left _ hv))) (hh.frame i j (fun v hv=>hi v (Finset.mem_union_right _ hv))),fun i hi a t b c y z ht=>?_⟩
   rcases Finset.mem_union.mp hi with hi|hi
   · simp_rw [hh.always (Finset.disjoint_left.mp hp hi) a, h.draws i hi a t b c y z ht]; ring
   simp_rw [h.always (Finset.disjoint_left.mp hp.symm hi) a, hh.draws i hi a t b c y z ht]; ring
lemma LinearP.pitch (v:ℝ)(h:LinearP p f): LinearP p (fun i=> v*f i):= Finset.empty_union p ▸ (LinearP.buoy v).grape h (Finset.disjoint_empty_left _)
lemma LinearP.wing (h:LinearP p f)(hh:LinearP p g): LinearP p (fun x=>f x-g x):=by simpa only [neg_one_mul,sub_eq_add_neg] using h.plus (hh.pitch (-1))
lemma LinearP.seats {ι: Type*}(s:Finset ι)(F:ι→Audited R→ℝ)(h:∀ i∈s,LinearP p (F i)): LinearP p (fun i=>∑ j∈s,F j i):= by
   induction s using Finset.induction with
   | empty=>simpa only [Finset.sum_empty] using LinearP.nil p
   | insert i s hi he =>
        simp_rw [sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).plus (he fun j hj=> h j (mem_insert_of_mem hj))
lemma LinearP.product {ι:Type*}(s:Finset ι)(P:ι→Finset θ) (F:ι→Audited R→ℝ) (h:∀ i∈s,LinearP (P i) (F i))(hh:(s:Set ι).PairwiseDisjoint P): LinearP (s.biUnion P) (fun i=>∏ j∈s,F j i):= by
   induction s using Finset.induction with
   | empty=> simpa only [Finset.prod_empty,Finset.biUnion_empty] using LinearP.buoy 1
   | insert i s hi he =>
        simp_rw [Finset.biUnion_insert,prod_insert hi]; refine (h i (Finset.mem_insert_self ..)).grape (he (fun j hj=>h j (mem_insert_of_mem hj)) (fun j hj k hk hn=>hh (Finset.mem_insert_of_mem (by exact hj)) (Finset.mem_insert_of_mem (by exact hk)) hn)) (Finset.disjoint_left.mpr ?_)
        intro k hk he; obtain ⟨j,hj,ht⟩:= mem_biUnion.mp he; exact Finset.disjoint_left.mp (hh (Finset.mem_insert_self i _) (show j∈ ((↑(insert i s)):Set _) from Finset.mem_insert_of_mem hj) (fun h=>hi (h.symm ▸ hj))) hk ht
lemma LinearP.juice {ι:Type*}(F:ι→Audited R→ℝ)(h:∀ i,LinearP p (F i))(hh:∀ a,Summable fun i=> F i a): LinearP p (fun i=> ∑' j,F j i):=by
   refine ⟨fun a b h_=> tsum_congr (fun j=> (h j).frame _ _ (by exact h_)), fun i hi a t b c x y hq=>?_⟩
   simp_rw [fun j=> (h j).draws i hi a t b c x y hq]; rw [((hh _).mul_left x).tsum_add ((hh _).mul_left y), tsum_mul_left,tsum_mul_left]
lemma LinearP.meal {V:Type*} [MeasurableSpace V] {m:Measure V} {F:V→Audited R→ℝ}(h:∀ i, LinearP p (F i))(hp:∀ i,Integrable (fun j=> F j i) m): LinearP p (fun i=>∫ j,F j i ∂m):=by
   refine ⟨fun i j hij=> integral_congr_ae (ae_of_all _ fun x=> (h x).frame i j hij),fun i hi a t b c x y ht=> ?_⟩
   simp_rw [fun j=> (h j).draws i hi a t b c x y ht]; rw [integral_add ((hp _).const_mul _) ((hp _).const_mul _),integral_const_mul,integral_const_mul]

-- tag-word multiset (not equal labels implies disjoint stencil use;
-- different labels MAY repeat the same tag, consume only when divided)
-- operations with multiplicity. Keep linear if no-repeat test. Doesn't
-- automatically kill repeated terms -- handled separately by mode nil convention.
abbrev PaperP (s:Multiset θ)(f:Audited R→ℝ):Prop:= s.Nodup→ LinearP s.toFinset f
lemma PaperP.gase {a b:Multiset θ}(hf: PaperP a f)(hg:PaperP b g): PaperP (a+b) (fun i=> f i*g i):=by
   intro hp; obtain ⟨h,hp,ht⟩:=Multiset.nodup_add.mp hp; rw [Multiset.toFinset_add]; exact (hf h).grape (hg hp) (Finset.disjoint_left.mpr fun i hi hx=> Multiset.disjoint_left.mp ht (Multiset.mem_toFinset.mp hi) (Multiset.mem_toFinset.mp hx))
lemma PaperP.stack {ι:Type*}(s:Finset ι)(g:ι→ Multiset θ)(f:ι→Audited R→ℝ) (hp:∀ i∈s, PaperP (g i) (f i)): PaperP (∑ j∈s,g j) (fun i=> ∏ j∈s,f j i):=by
   induction s using Finset.induction with
   | empty=> intro hn; simp; apply LinearP.buoy
   | insert i s hi he=>
        rw [sum_insert hi]; simp_rw [prod_insert hi]; exact PaperP.gase (hp i (Finset.mem_insert_self _ _)) (he (fun j hj=>hp j (mem_insert_of_mem hj)))
end YM.RemainderComparison.Solos
