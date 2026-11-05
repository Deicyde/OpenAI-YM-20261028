import YM.UVExtension.Wren.Tower
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Reseve
/-! First order continuation of ACTUAL labelled history. Transportation in l¹ of each stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Function Filter Finset Lattice Wilson MeasureTheory RG Push Push.AbsoluteSums
open Steady Wren Extra.Histories
open scoped BigOperators Topology ContDiff Classical
variable {κ ι α :Type}{v: Filter ι}{t:ℝ}
abbrev ram (f:ℝ→ℝ):ℝ:= |f t| +|deriv f t|
lemma dwProd (f g:ℝ→ℝ) (hf:DifferentiableAt ℝ f t)(hg:DifferentiableAt ℝ g t): ram (t:=t) (fun z=> f z*g z) ≤ ram (t:=t) f* ram (t:=t) g:=by
  unfold ram; rw [deriv_fun_mul hf hg,abs_mul]; apply le_trans (add_le_add_right (abs_add_le ..) _); rw [abs_mul,abs_mul]; nlinarith only [mul_nonneg (abs_nonneg (deriv f t)) (abs_nonneg (deriv g t))]
lemma dwAll (s : Finset κ)(f:κ→ℝ→ℝ)(hf:∀ i∈s,DifferentiableAt ℝ (f i) t) : ram (t:=t) (fun z=>∏ i∈s, f i z) ≤ ∏ i∈s, ram (t:=t) (f i):=by
   induction s using Finset.induction with
   | empty => simp only [prod_empty]; simp [ram]
   | insert i s hi hp=>
      have ht j (hj:j∈s) := hf j (mem_insert_of_mem hj)
      simp_rw [prod_insert hi]; exact (dwProd _ _ (hf i (mem_insert_self ..)) (DifferentiableAt.fun_finsetProd ht)).trans (mul_le_mul_of_nonneg_left (hp ht) (by unfold ram; positivity))
lemma dwPow (f:ℝ→ℝ)(hf:DifferentiableAt ℝ f t)(b:ℕ)(c:ℝ) : ram (t:=t) (fun z=> f z^b/c) ≤ ram (t:=t) f^b / |c|:=by
   have hh:= dwAll (Finset.univ (α:=Fin b)) (fun _=>f) (fun _ _=> hf); simp only [prod_const,card_univ,Fintype.card_fin] at hh
   simp_rw [div_eq_mul_inv]; exact (dwProd _ _ (hf.fun_pow b) (differentiableAt_const _)).trans (mul_le_mul hh (by simp [ram]) (add_nonneg (abs_nonneg _) (abs_nonneg _)) (pow_nonneg (by unfold ram; positivity) _))

structure Finely (f:ι→α→ℝ→ℝ) : Prop where
   diff : ∀ n a, DifferentiableAt ℝ (f n a) t
   pay : Tune v (fun n a=> f n a t)
   lives : Tune v (fun n a=> deriv (f n a) t)
namespace Finely
variable {f g:ι→α→ℝ→ℝ}
lemma scales (hf:Finely (t:=t) (v:=v) f)(hg:Finely (t:=t) (v:=v) g): Finely (t:=t) (v:=v) (fun n a z=> f n a z * g n a z):=by
   refine ⟨fun n a => (hf.diff n a).mul (hg.diff n a),hf.pay.mul hg.pay,?_⟩; simp_rw [fun n a=> deriv_fun_mul (hf.diff n a) (hg.diff n a)]; exact (hf.lives.mul hg.pay).add (hf.pay.mul hg.lives)
lemma base (c:ℝ): Finely (t:=t) (v:=v) (fun _ (_:α) _=> c):=by refine ⟨fun n _=> differentiableAt_const _,Tune.constant _ c tendsto_const_nhds,?_⟩; simp only [deriv_const]; exact Tune.nil
lemma livesP (h:Finely (v:=v) (t:=t) f) (k:ℕ) (c:ℝ): Finely (v:=v) (t:=t) (fun n a z=> f n a z^k/c):=by
    have hx(k:ℕ): Finely (v:=v) (t:=t) (fun n a z=> f n a z^k):=by
       induction k with
       | zero=> simp only [pow_zero]; exact base _
       | succ k ih=> simp only [pow_succ]; exact ih.scales h
    simp only [div_eq_mul_inv]; exact (hx k).scales (base _)
lemma sets (s:Finset κ)(f:κ→ι→α→ℝ→ℝ)(h:∀ i∈s,Finely (v:=v) (t:=t) (f i)): Finely (v:=v) (t:=t) (fun n a z=> ∏ i∈s,f i n a z):=by
    induction s using Finset.induction with
    | empty=> simp only [prod_empty]; exact base _
    | insert i s hi hn=> simp_rw [prod_insert hi]; exact (h i (mem_insert_self ..)).scales (hn fun i hi=> h _ (mem_insert_of_mem hi))
end Finely
open Multiple
structure Canted (v:Filter ι)(t:ℝ)(f:ι→κ→α→ℝ→ℝ):Prop where
   firms : ∀ n k a, DifferentiableAt ℝ (f n k a) t
   well : Transit v (fun n k a=> f n k a t)
   joys : Transit v (fun n k a=> deriv (f n k a) t)
namespace Canted
variable {f:ι→κ→α→ℝ→ℝ}
lemma ever (f:ι→κ→α→ℝ)(h:Transit v f): Canted v t (fun n k a _=> f n k a):=by refine ⟨fun i k a=> differentiableAt_const _,h,?_⟩; simp_rw [deriv_const]; exact Transit.zero
lemma bay (h:Canted v t f) (i:κ): Finely (v:=v) (t:=t) (fun n=> f n i):=⟨fun n a=> h.firms n i a,h.well.meters _,h.joys.meters _⟩
lemma tools (h:Canted v t f):∃ b,Swift v b∧ ∀ᶠ n in v,∀ i a,ram (t:=t) (f n i a)≤ b n i:=by
   obtain ⟨b,hb,h'⟩:=h.well.rain; obtain ⟨c,hc,hK⟩:=h.joys.rain; exact ⟨_,hb.plus hc,(h'.and hK).mono fun n h i a=>add_le_add (h.1 i a) (h.2 i a)⟩
lemma grapes (h:Canted v t f): Canted v t (fun n j a z=> manyW (fun i=> f n i a z) j):=by
   let H(i:Reps κ):= Finely.sets (Finset.univ (α:=↥i.1)) _ (fun j _=> (h.bay j.val).livesP (i.2 j+1) ((i.2 j+1).factorial:ℝ))
   refine ⟨fun n j a=> (H j).diff n a, Sheets.boil _ h.well,⟨?_,fun i=> (H i).lives⟩⟩
   obtain ⟨b,hb,h'⟩:= h.tools; obtain ⟨c,hc⟩:= hb.books; refine ⟨_,hb.repetitions,?_⟩; filter_upwards [h',hc] with n hn ht i a
   let g z:= manyW (fun i=> f n i a z) i; have hp: ‖deriv g t‖≤ ram (t:=t) g:=le_add_of_nonneg_left (abs_nonneg _); apply hp.trans
   unfold g manyW; apply (dwAll _ (fun j z=> f n (j:↥i.1).val a z^(i.2 j+1)/(↑((i.2 j+1).factorial):ℝ)) (fun i _=> ((h.firms n _ a).fun_pow _).div_const _)).trans
   refine Finset.prod_le_prod (fun _ _=> add_nonneg (abs_nonneg _) (abs_nonneg _)) (fun j _=>?_); apply (dwPow _ (h.firms _ _ _) _ _).trans; rw [abs_of_pos (show (0:ℝ)< ↑((i.2 j+1).factorial) from by positivity)]
   exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hn _ a) _) (by positivity)
lemma goods (h:Canted v t f): Canted v t (fun n j a z=> ∏ i∈j,f n i a z):=by
   let H(i:Finset κ):= Finely.sets i (fun j n a=> f n j a) (fun j _=> h.bay j)
   obtain ⟨b,hb,hK⟩:= h.tools; obtain ⟨c,hc⟩:= hb.books; have hh : ∀ᶠ n in v,∀ j a, ram (t:=t) (fun z=> ∏ i∈j,f n i a z) ≤ ∏ i∈j,b n i:= (hK.and hc).mono fun n hn j a => (dwAll _ _ (fun i _=> h.firms n i a)).trans (Finset.prod_le_prod (fun _ _=>add_nonneg (abs_nonneg _) (abs_nonneg _)) (fun j _=> hn.1 _ _))
   exact ⟨fun n k a=> (H k).diff n a,⟨⟨_,hb.powerList, hh.mono (fun n h k a=> (le_add_of_nonneg_right (abs_nonneg _)).trans (h k a))⟩, fun i=> (H i).pay⟩,⟨⟨_,hb.powerList,hh.mono (fun n h k a=> (le_add_of_nonneg_left (abs_nonneg _)).trans (h k a))⟩, fun i=> (H i).lives⟩⟩
lemma join {β:Type}{g:ι→β→α→ℝ→ℝ}(hf:Canted v t f)(hg:Canted v t g): Canted v t (fun n x=> Sum.elim (f n) (g n) x):=by
   refine ⟨fun n x a=>?_, (hf.well.merge hg.well).fade ?_,(hf.joys.merge hg.joys).fade ?_⟩; cases x; exact hf.firms ..; exact hg.firms ..
   all_goals filter_upwards with n i; cases i <;> rfl
lemma lite (b:κ→α→Prop)[∀ k,DecidablePred (b k)](hf:Canted v t f): Canted v t (fun n k a z=> if b k a then f n k a z else 0):=by -- instance ambig
   refine ⟨fun n k a=>?_, hf.well.masks b,(hf.joys.masks b).fade (Eventually.of_forall fun n k=> funext fun a=>?_)⟩
   · split; exact hf.firms ..; exact differentiableAt_const _
   split <;> next h=>simp [h]
lemma lenses {β:Type}(b:β→κ)(hb:Injective b)(h:Canted v t f): Canted v t (fun n k=> f n (b k)):=⟨fun n k i=> h.firms n (b k) i,h.well.many b hb fun _=>id,h.joys.many b hb fun _=>id⟩
open Progress.DirectedRecipe
end Canted
end YM.UVExtension.Wet
