import YM.AnalyticNext.CUBIC_MATCH.Ledger.Figures
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Collective
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Polish
import YM.Extra.FREE_DETECTOR_ALGEBRA.GradedBasis
import YM.MergeProof.Badlands
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Compression
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Spinto
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stagecraft
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Fund
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Infinite
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Comparison
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Hybrid
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Marginal
import YM.Push.LOOP_COEFFICIENT.ContinuumTrace
/- MVT interpolation in fixed finite but possibly large interpolation stencil; we can oversample. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Acme
open Filter Function Set Real
open scoped Topology BigOperators ContDiff Classical
variable (k:ℕ)(p:ℝ)
def arced (x:Fin (2^k)→ℝ):Prop:= (∀ i,x i∈ Icc (-p) p) ∧ ∀ i j,i<j→ x i+1≤ x j
lemma amph (hp:0<p): ∃ A:ℝ,0<A∧∀ (f:ℕ→ℝ→ℝ)(ε:ℝ)(x: Fin (2^k)→ℝ),0<ε →arced k p x→ (∀ w, ‖f 0 (x w)‖≤ε)→ (∀ i<k,∀ y∈ Icc (-p) p, HasDerivAt (f i) (f (i+1) y) y)→ (∀ y∈Icc (-p) p,‖f k y‖ ≤ ε) → ∀ y∈ Icc (-p) p,‖f 0 y‖ ≤ ε*A:=by
   induction k with
   | zero=> exact ⟨1,zero_lt_one,fun f e x he hx hv h hp y hy => (hp y hy).trans_eq (mul_one e).symm⟩
   | succ n ih=>
      obtain ⟨A,hA,H⟩:= ih; refine ⟨1+4*p*A,by positivity,fun f ε x hε hx hv hF hN y hy => ?_⟩
      let L(i:Fin (2^n)):Fin (2^(n+1)):=⟨i.val*2,by rw [pow_succ]; have := i.isLt;omega⟩
      let K(i:Fin (2^n)):Fin (2^(n+1)):=⟨i.val*2+1,by rw [pow_succ]; have := i.isLt;omega⟩
      have hh:∀ y∈Icc (-p) p,HasDerivAt (f 0) (f 1 y) y:=hF 0 (Nat.zero_lt_succ _)
      have ht (i: Fin (2^n)):∃ r ∈ Ioo (x (L i)) (x (K i)), ‖f 1 r‖ ≤ 2*ε :=by
          have hu:=hx.2 (L i) (K i) (show _<_ from Nat.lt_add_one _)
          have hp' : x (L i)<x (K i):=by linarith
          have he := Icc_subset_Icc (hx.1 (L i)).1 (hx.1 (K i)).2
          obtain ⟨r,hr,he'⟩:=exists_deriv_eq_slope (f 0) hp' (fun v h=> (hh v (he h)).continuousAt.continuousWithinAt) (fun v h=> (hh v (he (Ioo_subset_Icc_self h))).differentiableAt.differentiableWithinAt)
          rw [(hh r (he (Ioo_subset_Icc_self hr))).deriv] at he'
          refine ⟨r,hr,?_⟩; rw [he',norm_div, Real.norm_of_nonneg (sub_pos.mpr hp').le,div_le_iff₀ (sub_pos.mpr hp')]
          refine (norm_sub_le ..).trans ?_; nlinarith [hv (K i),hv (L i)]
      choose r hr hR using ht
      have he: arced n p r:=by
         refine ⟨fun i=> Icc_subset_Icc (hx.1 (L i)).1 (hx.1 (K i)).2 (Ioo_subset_Icc_self (hr i)),fun i j h=>?_⟩
         refine le_trans (add_le_add_left (hr i).2.le 1) (?_)
         exact (hx.2 _ _ (show K i < L j from (by change i.val*2+1<j.val*2;exact (by have := Fin.lt_iff_val_lt_val.mp h;omega)))).trans (hr j).1.le
      have hz := H (fun i=>f (i+1)) (2*ε) r (by positivity) he hR (fun i hi=> hF (i+1) (by omega)) (fun y hy=> (hN y hy).trans (by linarith))
      let w: Fin (2^(n+1)):=⟨0,pow_pos (by omega) _⟩
      have hD:= Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜:=ℝ) (fun y hy=>(hh y hy).hasDerivWithinAt) hz (convex_Icc _ _) (hx.1 w) hy
      have ht: ‖y-x w‖ ≤2*p:=by rw [Real.norm_eq_abs];exact abs_le.mpr ⟨by linarith only [hy.1,(hx.1 w).2], by linarith only [hy.2,(hx.1 w).1]⟩
      have hs: ‖f 0 y - f 0 (x w)‖ ≤ 2*ε*A*(2*p):= hD.trans (mul_le_mul_of_nonneg_left ht (by positivity))
      linarith only [hs, norm_add_le (f 0 y-f 0 (x w)) (f 0 (x w)), norm_sub_norm_le (f 0 y) (f 0 (x w)), hv w]
lemma angel (hp:0<p):∃ A:ℝ,0<A∧∀ (f:ℕ→ℝ→ℂ)(ε:ℝ)(x: Fin (2^k)→ℝ),0<ε →arced k p x→ (∀ w, ‖f 0 (x w)‖ ≤ ε)→ (∀ i<k,∀ y∈ Icc (-p) p, HasDerivAt (f i) (f (i+1) y) y)→ (∀ y∈Icc (-p) p,‖f k y‖ ≤ ε) → ∀ y∈ Icc (-p) p,‖f 0 y‖ ≤ ε*A:=by
    obtain ⟨a,ha,hA⟩:= amph k p hp
    refine ⟨a+a,add_pos ha ha,fun f ε x he hh hW hf ht y hy =>?_⟩
    have hr : |(f 0 y).re|≤ ε*a:= hA (fun i y=> (f i y).re) ε x he hh (fun w=> (Complex.abs_re_le_norm _).trans (hW w)) (fun i hi y hy=> Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hf i hi y hy)) (fun v hv=> (Complex.abs_re_le_norm _).trans (ht v hv)) y hy
    have hp : |(f 0 y).im|≤ ε*a:= hA (fun i y=> (f i y).im) ε x he hh (fun w=> (Complex.abs_im_le_norm _).trans (hW w)) (fun i hi y hy=> Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hf i hi y hy)) (fun v hv=> (Complex.abs_im_le_norm _).trans (ht v hv)) y hy
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)
end YM.MergeProof.Acme
