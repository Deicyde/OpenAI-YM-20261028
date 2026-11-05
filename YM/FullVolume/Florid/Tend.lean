import YM.MergeProof.SwitchCost
import YM.FullVolume.Sym.Fade
/-!
 # True polynomial views. `Marker jet` AND aperture analyt along β-phase.
 No normalization by gas denominator. Signed palette.Burden pull. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray.Weigh
open Function Filter Set Finset MeasureTheory Merge Merge.Switch PhysicalNext.Repeat PhysicalNext.Repeat.Jams
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {U A β:Type}[Fintype A]
-- on aperture λ.Jet exact + analytic, Models not explicit for offscreen.
abbrev Trail (U A:Type):Type:= sun→U→Ways A
def Strung (f:Trail U A)(r a:ℝ):Prop:=1≤ r ∧ ∃ v:Score A, (∀ i,0≤ v i) ∧ high v ≤ a ∧ (∀ t: sun,∀ i:U,∃ g,Switch.Models (f t i) g) ∧ ∀ i:Finset A,∀ u, Scout r (phraseS fun t=> jet (f t u) i) (v i)
namespace Strung
variable {r a b y:ℝ} {p: Finset A}{f g:Trail U A}
lemma tame (h:Strung f r a) (he:a≤b):Strung f r b:=by obtain ⟨x,v,hf,hk,hg,h⟩:= h;exact ⟨x,v,hf,hk.trans he,hg,h⟩
lemma bright (h:Strung f r a) (hp:1≤ b) (he:b≤r):Strung f b a:=by obtain ⟨x,v,hf,hk,hg,h⟩:= h;exact ⟨hp,v,hf,hk,hg,fun i l=> (h i l).lessen hp he⟩
lemma toll (h:Strung f r a):0≤ a:= by obtain ⟨x,v,hk,hp,h⟩:= h; exact (sum_nonneg fun i _=>hk i).trans hp
lemma tapes (h:Strung f r a)(i: Finset A)(y:U): Scout r (phraseS fun t=> jet (f t y) i) a:=by obtain ⟨r,v,hv,hP,H,h⟩:=h; exact (h i y).enlarged (le_trans (single_le_sum (fun u _=>hv u) (Finset.mem_univ i)) hP)
lemma radius (h:1≤r) {Q:sun→ U→ℝ} (hb: 0≤a) (hr:∀ i:U, Scout r (phraseS fun t=>Q t i) a) (i:Finset A):
    Strung (U:=U) (A:=A) (fun t u=> Switch.click i (Q t u)) r a:=by
   let x(p: Finset A):= if p=i then a else 0; have hX p:0 ≤ x p:=by unfold x;split;exact hb;rfl
   refine ⟨h,x,hX,by simp [high,x],fun t u=>⟨_,modelClick i _⟩,fun k U=>?_⟩
   simp_rw [fun c=> (Switch.modelClick i c).exact]; by_cases hp:k=i
   · subst k; simpa only [Switch.bench,x, ↓reduceIte] using hr U
   simp only [x, hp, ↓reduceIte,bench];exact (Scout.still h (0:ℝ)).enlarged (le_of_eq norm_zero)
lemma foyer (h:1≤r) {Q:sun→ U→ℝ}(hb:0 ≤ a)(hr:∀ i:U, Scout r (phraseS fun t=> Q t i) a) : Strung (A:=A) (fun t u _ _=>Q t u) r a:=by
   convert! radius h hb hr (∅:Finset A) using 1; ext; simp [click]
lemma leaf (h:1≤r)(a:ℝ): Strung (U:=U) (A:=A) (fun _ _ _ _=>a) r ‖a‖:= foyer h (norm_nonneg _) fun _=> Scout.still h a
lemma none (h:1≤r): Strung (0:Trail U A) r 0:= by rw [← norm_zero (E:=ℝ)];exact leaf h _ -- rewrite issue
lemma zenith (h:1≤r): Strung (1:Trail U A) r 1:=by have hh:= (leaf (U:=U) (A:=A) h 1); rw [norm_one] at hh; exact hh -- issues defeq. use convert
lemma verge (h:Strung f r a)(hp:Strung g r b): Strung (f+g) r (a+b):=by
   obtain ⟨r',v,hv,hV,hx,h⟩:=h; obtain ⟨hc,k,hk,hK,hU,hp⟩:=hp
   choose p H using hx; choose q H' using hU; refine ⟨r',v+k,fun i=>add_nonneg (hv _) (hk _),by unfold high; simp only [Pi.add_apply,Finset.sum_add_distrib]; exact add_le_add hV hK,fun t U=>⟨_,(H t U).add (H' t U)⟩,fun i U=>?_⟩ -- edit sum
   apply ((h i U).pair (hp i U)).replace; intro t ht; let t':sun:=⟨t,ht⟩; unfold phraseS; let a:=pinch t; let hp:= H a U; let hx:= H' a U; change jet (f a U) i+jet (g a U) i=jet (f a U+g a U) i; rw [hp.exact,hx.exact,(hp.add hx).exact];rfl
lemma vigor (h:Strung f r a)(hp:Strung g r b):Strung (f*g) r (a*b):=by
   obtain ⟨r',v,hv,hV,hx,h⟩:=h; obtain ⟨hc,k,hk,hK,hU,hp⟩:=hp
   choose p H using hx; choose q H' using hU; refine ⟨r',comb 1 v k,comb_nn _ _ hv hk,by rw [colors]; exact mul_le_mul hV hK (sum_nonneg fun i _=> hk _) ((sum_nonneg fun i _=>hv i).trans hV), fun t U=>⟨_,(H t U).mul (H' t U)⟩,fun i U=>?_⟩
   let V (t:sun):= jet (f t U);let W(t:sun):=jet (g t U)
   let F(x:Finset A ×Finset A)(t:ℝ):= if i=x.1∪x.2 then (0:ℝ)^(x.1∩x.2).card* V (pinch t) x.1 *W (pinch t) x.2 else 0
   let a (x:Finset A × Finset A):= if i=x.1∪x.2 then (1:ℝ)^(x.1∩x.2).card *v x.1 *k x.2 else 0
   have hh x: Scout r (F x) (a x):=by
        unfold F a; split_ifs
        · let i:ℕ:= (x.1∩x.2).card; refine (((h _ U).scale ((0:ℝ)^i)).multiplies (hp (x.2) U)).enlarged ?_
          rw [one_pow,one_mul]; apply mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hv _) (by rw [Real.norm_eq_abs, abs_pow,abs_zero]; exact pow_le_one₀ le_rfl zero_le_one)) (hk _)
        exact (Scout.still r' (0:ℝ)).enlarged (le_of_eq norm_zero)
   apply (Scout.pieces univ F a r' (fun i _=>hh i)).replace; intro t ht; let s:=pinch t
   have hz:= H s U;have ht:= H' s U
   change (∑ i,F i t)=jet (f s U*g s U) i; rw [(hz.mul ht).exact]; rw [← hz.exact,← ht.exact]; convert! (Eq.refl (comb 0 (jet (f s U)) (jet (g s U)) i)) -- typeclasses.
lemma train (h:Strung f r a)(y:ℝ):Strung (y • f) r (‖y‖ * a) := vigor (leaf h.1 y) h
lemma assembly (x:Finset β)(g:β→Trail U A)(v:β→ℝ) (hp:1≤r)(h:∀ i∈x,Strung (g i) r (v i)): Strung (∑ i∈x,g i) r (∑ i∈x,v i):=by
   induction x using Finset.induction with
   | empty=> simp only [sum_empty]; exact Strung.none hp
   | insert i x hi hx => rw [sum_insert hi,sum_insert hi]; exact verge (h i (mem_insert_self ..)) (hx fun i hi=> h i (mem_insert_of_mem hi))
lemma winds (x:Finset β)(g:β→Trail U A)(v:β→ℝ) (hp:1≤r)(h:∀ i∈x,Strung (g i) r (v i)): Strung (∏ i∈x,g i) r (∏ i∈x,v i):=by
   induction x using Finset.induction with
   | empty=> rw [Finset.prod_empty,Finset.prod_empty]; exact zenith hp
   | insert i x hi hx => rw [prod_insert hi,prod_insert hi]; exact vigor (h i (mem_insert_self ..)) (hx fun i hi=> h i (mem_insert_of_mem hi))
lemma rolls (h:Strung f r a)(i:ℕ): Strung (f^i) r (a^i) :=by
   induction i with | zero => rw [pow_zero,pow_zero];exact zenith h.1 | succ i ih=>rw [pow_succ,pow_succ];exact ih.vigor h
-- gating by parameter-INDEPENDENT actual config
lemma cloud (h:Strung f r a)(p:U→Prop): Strung (fun t U=>if p U then f t U else 0) r a:=by
   obtain ⟨ha,v,hv,hV,hP,h⟩:= h; refine ⟨ha,v,hv,hV,fun t U=>?_,fun i U=>?_⟩
   · dsimp only; split; exact hP ..; exact ⟨0,⟨fun x _=>funext fun i=>by simp [Switch.value],fun v=>tendsto_const_nhds⟩⟩
   dsimp only; split_ifs
   · exact h ..
   have hZ:Models (0:Ways A) 0:=⟨fun x _=> funext fun i=>by simp [Switch.value], fun v=>tendsto_const_nhds⟩
   change Scout r (phraseS fun _=>jet (0:Ways A) i) (v i); rw [hZ.exact]; exact (Scout.still ha (0:ℝ)).enlarged (norm_zero.trans_le (hv _))
end Strung
end YM.FullVolume.Ray.Weigh
