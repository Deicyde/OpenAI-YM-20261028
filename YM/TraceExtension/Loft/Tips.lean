import YM.TraceExtension.Loft.Drifts
import YM.TraceExtension.Lamp.Outpost
/-!
# Pole leg extraction with compact routines. Period limit before µ tilt down.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Perfect
open scoped BigOperators Topology ContDiff ComplexConjugate
variable {W α β : Type} [Fintype α] {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n:ℕ}{σ τ A C D μ δ ε a r:ℝ}
def yard (d i:Axis)(q:G.ColorIndex)(F:Maze G f):= (Fintype.card (Site f):ℂ)⁻¹*Lamp.cob d i q F
def acePay (X:Award G)(q:G.ColorIndex)(d:Axis)(p:Momentum):ℂ:= stock (X (coord d,q) (coord d,q) p)
variable {X:Award G}{F:Maze G f}
lemma traveler_s {i:Axis}{v:G.ColorIndex}(p q:Momentum)(hp:star p=p)(h:Firm σ A (starTrack (X (coord i,v) (coord i,v))))(hk:rolls p q): acePay X v i p=acePay X v i q:=by
    have ht:=fireworks _ h (half_pos h.width_pos) (by linarith[h.width_pos]); exact hk.apply ht (ht.in_range hp)
variable {g:W→Side}{L: Filter W}
lemma tipped (Q:Tendsto (fun w=>(g w).val) L atTop)(hs:0<σ)(n:ℕ)(A:ℝ): Tendsto (fun i=>(pitchf (g i))⁻¹^n*(A*Real.exp (-(σ/4)* (g i).val))) L (𝓝 0):=by
    let t(i:W):ℝ:= σ/4 * ↑((g i).val); have H:= Tendsto.const_mul_atTop (r:=σ/4) (by positivity) (tendsto_natCast_atTop_atTop.comp Q)
    let V:=((σ/4)*(2*Real.pi))^n; have hV:0 < V:=by unfold V; positivity
    have h:=(((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp (show Tendsto t L atTop from H)).div_const V).const_mul A
    rw [_root_.zero_div,mul_zero] at h; apply h.congr'; filter_upwards with i
    change A * ((t i^n*Real.exp (-t i))/V)=_
    have hm:0 < ((g i).val:ℝ):= Nat.cast_pos.mpr (g i).property
    have hv: t i=(pitchf (g i))⁻¹*((σ/4)*(2*Real.pi)):=by unfold t pitchf; field_simp
    rw[show -(σ/4)* ↑(g i).val= -(t i) from neg_mul .., show t i^n=_ from (congr_arg (fun x:ℝ=>x^n) hv).trans (mul_pow ..)]
    change A*((((pitchf (g i))⁻¹^n * V)*Real.exp _)/V)=_; field_simp
lemma honor_fm {K:W→ Phase α→ℂ}(h:∀ i,Firm σ A (K i)): Honor (fun i=>K i ∘ axes) n:=by
    let M: Corn α→L[ℝ] Phase α:= ContinuousLinearMap.pi fun a=>Complex.ofRealCLM ∘L ContinuousLinearMap.proj a
    let t j:=A*circleTax σ j * ‖M‖^j; refine ⟨∑ i∈range (n+1),|t i|, sum_nonneg fun i _=>abs_nonneg _, fun w x=>?_⟩
    exact ⟨((h w).analytic_real x).contDiffAt,fun k hk=>le_trans (toast_into (h w) M x (axes_real _) _) ((le_abs_self (t k)).trans (single_le_sum (s:=range (n+1)) (f:=fun i=>|t i|) (fun i _=>abs_nonneg _) (mem_range.mpr (by omega))))⟩
lemma payday (q:G.ColorIndex)(d i:Axis) (Q:Tendsto (fun w=>(g w).val) L atTop)(X:W→ Award G)(P:∀ w,Maze G (g w)) (hs:0 < σ)(hA:0 ≤ A)(h:∀ w a b,Firm σ A (starTrack (X w a b)))(hp:∀ w,Awards (X w) (P w)): Rose L (fun w=> yard d i q (P w)) (fun w=> neap 2 (acePay (X w) q i ∘ axes) 0 (step d)):=by
    let k:Loc G 1:=(coord i,q); let Y w:= X w k k; let V(w):= acePay (X w) q i; let t(i:W):= pitchf (g i);let K(w)(j:ℤ):=(wrap (g w) (ra d j))
    let Z w j:=shop (g w) (Y w (mon (-(K w j)))); let x(w:W)(j:ℤ):= t w • ((j:ℝ) • (-(step d:Track))); have hw(w):Firm (σ/2) A (V w):=fireworks _ (h w k k) (half_pos hs) (by linarith)
    have hx(w): yard d i q (P w)=PanZ (fun j:ℤ=> ((t w:ℂ)⁻¹)^(2:ℕ)*Z w j):=by
       let N:ℂ:=Fintype.card (Site (g w)); have hN:N≠0:=Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
       unfold yard Lamp.cob; rw[← smul_eq_mul,← map_smul]; apply congr_arg _; funext j
       change N⁻¹*(((t w:ℂ)⁻¹)^ (2:ℕ)*clipP i q (P w) (K w j) (-(K w j)))=_; unfold clipP; rw [hp w, if_pos (add_neg_cancel _),show ((cents (g w):ℝ):ℂ)= N by simp [N,cents]]; change _=_*Z w j; field_simp; rfl
    simp_rw[hx]; let U(w):= V w∘ axes
    have he(j:ℤ): Rose L (fun w=> ((t w:ℂ)⁻¹)^ (2:ℕ)*Z w j) (fun w=> ((t w:ℂ)⁻¹)^ (2:ℕ)*U w (x w j)):=by
       refine squeeze_zero_norm' ?_ (tipped Q hs 2 (royalty σ A)); filter_upwards with w; dsimp only[Pi.sub_apply]; rw[← mul_sub,norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg (pitch_pos (f:=g w)|>.le)]; refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
       let v:=mon (-(K w j)); have hR:rolls v (axes (x w j)):=by
           have ht:= reel_roll (g w) (-(ra d j)); rw[map_neg,reel_neg, ra, reel_z,reel_i] at ht; unfold x; rw [smul_neg, smul_neg]; rw[smul_neg] at ht; exact ht
       have hl:= traveler_s v _ (real_frequency _) (h w k k) hR
       rw [show U w (x w j)=_ from hl.symm]; exact Firm.tryout (stock_take (Y w) (h w k k) (hp:=Work.F07.realStrip σ hs (real_frequency _))) (g w)
    apply Rose.chain (pan_coh (F:=fun w j=> ((t w:ℂ)⁻¹)^ (2:ℕ)*Z w j) (H:=fun w j=> ((t w:ℂ)⁻¹)^ (2:ℕ)*U w (x w j)) he)
    refine Rose.chain (pan_brief (gran Q) U (-step d) (honor_fm hw)) (Rose.skip ?_); filter_upwards with w; simpa using (neap_tide (U w) 2 0 (step d) (-1))
lemma leapsL (q:G.ColorIndex)(d i:Axis)(h:∀ i j, Firm σ A (starTrack (X i j))) (hs:0 < σ): neap 2 (acePay X q i∘ axes) 0 (step d)=(2:ℂ)*leapTip (profitable X) (step d) i ![q,q]:=by
    let P:= pressLens (profitable X) ![q,q] i i; let U:=acePay X q i ∘ axes
    have he: P=fun v=> (1/2:ℝ) • U v:=by funext j; rw [Complex.real_smul]; push_cast; simp [one_div]; rfl
    have hp:=fireworks _ (h (coord i,q) (coord i,q)) (half_pos hs) (by linarith)
    change neap 2 U 0 (step d)= (2:ℂ)*neap 2 P 0 (step d)
    unfold neap; rw[show P=(1/2:ℝ) • U from he,iteratedFDeriv_const_smul_apply (f:=U) (hp.analytic_real _|>.contDiffAt)]; simp only [_root_.smul_apply,Complex.real_smul]; push_cast; ring
end YM.Trace.Loft
