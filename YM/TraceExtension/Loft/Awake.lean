import YM.TraceExtension.Loft.Exalt
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W:Type}{g:W→ Side}{L: Filter W}{G:Gauge}{U:Skuta W G}{V:Jar G}{p:Clip}{R:W→PathData G}{k m n:ℕ}{σ ε A α A' C D a C':ℝ}{B:(w:W)→Dart G (g w)}{ε':W→ℝ}
variable (q:G.ColorIndex)(h:Cred g p R U V σ ε A C D)(ht:Scene g B p R a C' ε')(Q:Tendsto (fun w=>(g w).val) L atTop)(hq:Tendsto ε' L (𝓝 0))(hM:Flare g R p α A')(he:G.Simple)
abbrev landPay (G:Gauge) := -(12:ℝ)*G.slopeConstant
abbrev seaD (p:Clip)(R:PathData G)(q:G.ColorIndex)(f:Side)(μ:ℝ):ℂ:=(μ:ℂ)^(2:ℕ)*suite (fun d i=> umbra d i q p R μ f)
section onset
include h Q hM he
lemma coastMark :∃ A : ℝ,0 ≤ A ∧ ∀ (a b:ℝ), a < b→ b ≤ 0 → ∃ (μ:W→ℝ), (∀ w,Real.exp a ≤ μ w∧ μ w≤ Real.exp b) ∧ ∀ᶠ w in L, |(seaD p (R w) q (g w) (μ w)).re-landPay G| ≤ A/(b-a):=by
    obtain ⟨A,hA,H⟩:= slopeL q Q h hM he
    refine ⟨A+A,by linarith,fun t u ht hu=>?_⟩
    let A'(w)(x:ℝ):=(ridge q p (R w) (Real.exp x) (g w)).re; let U(w)(x:ℝ):= - (seaD p (R w) q (g w) (Real.exp x)).re
    have hp(w)(x): HasDerivAt (A' w) (U w x) x:=by
       let N:= Real.exp x
       choose B y s D h' hS hh hv using hM.tanks
       have hn:0 < N:= Real.exp_pos x
       let p':= (hull_m (μ:=N) hn le_rfl (h' w) (hS w) (hh w) (hv w)).1.det_pos.ne'
       let z:= suite (fun d i=> umbra d i q p (R w) N (g w))
       have ht:= Complex.reCLM.hasFDerivAt.comp_hasDerivAt x ((ridge_deriv q (h' w) hn p').scomp x (Real.hasDerivAt_exp x)); apply Eq.mp _ ht; apply congr_arg (fun z=> HasDerivAt (A' w) z x)
       change (N • (-(N:ℂ)*z)).re = -( (↑N:ℂ)^ (2:ℕ) * z).re; rw[Complex.real_smul,← Complex.neg_re]; ring_nf
    choose c hc hv using fun w => exists_hasDerivAt_eq_slope (A' w) (U w) ht (fun i hi=> (hp w i).continuousAt.continuousWithinAt) (fun i _=> hp w i)
    have hL(x:ℝ)(hx:x ≤ 0): ∀ᶠ w in L, |A' w x+landPay G*x| ≤ A:=by
       filter_upwards [H (Real.exp x) (Real.exp_pos _) (by simpa)] with w hw; apply le_trans ?_ hw; unfold A' landPay; rw [Real.log_inv, Real.log_exp]; apply le_of_eq; congr 1; ring
    refine ⟨fun w=>Real.exp (c w),fun w=> ⟨Real.exp_le_exp.mpr ((hc w).1.le), Real.exp_le_exp.mpr (hc w).2.le⟩,?_⟩; filter_upwards [hL _ (ht.le.trans hu),hL u hu] with w h1 h2
    let y:= (seaD p (R w) q (g w) (Real.exp (c w))).re; let L:=landPay G; have hk:= sub_pos.mpr ht; have hu: (A' w u-A' w t)/(u-t)= -y:= (hv w).symm
    change |y-L| ≤ _; rw[show y-L= ((A' w t+L*t)-(A' w u+L*u))/(u-t) by rw[eq_div_iff hk.ne']; rw [div_eq_iff hk.ne'] at hu; linarith,abs_div,abs_of_pos hk]; apply div_le_div_of_nonneg_right _ hk.le; exact (abs_sub ..).trans (add_le_add h1 h2)
include ht hq
lemma awake (hα:0 < α): Tendsto (fun w=> (xup q (fun b=> lush ((B w).Y b 0) ∘ input G (g w))).re) L (𝓝 (landPay G)):=by
    obtain ⟨A,hA,H⟩:= coastMark q h Q hM he
    obtain ⟨B',hB,P⟩:=reprise q h ht Q hq hM he
    let X(w):= xup q (fun b=> lush ((B w).Y b 0) ∘ input G (g w))
    rw [Metric.tendsto_nhds]; intro ε he'
    obtain ⟨u,hu,hK⟩:∃ u:ℝ,u≤ 0 ∧ B'*Real.exp u ≤ ε/4:=by
        have he':0 < ε/4:=by positivity
        have ht: Tendsto (fun u:ℝ=> B'* Real.exp u) atBot (𝓝 0):=by simpa using Real.tendsto_exp_atBot.const_mul B'
        exact ((eventually_le_atBot 0).and (ht.eventually (ge_mem_nhds he'))).exists
    let C:= (A+1)/(ε/4); have hC:0 < C:=by unfold C; positivity
    obtain ⟨μ,H',hk⟩:= H (u-C) u (sub_lt_self u hC) hu; let M':=Real.exp (u-C);have hMp:0 < M':=Real.exp_pos _
    have hv(i): M'≤ μ i∧ μ i≤1:= ⟨(H' i).1,(H' i).2.trans (by simpa using hu)⟩
    have hh:= saga q Q he ht hM hα hMp hv hq
    let M(w):= (μ w:ℂ)^ (2:ℕ); let p'(w):= seaD p (R w) q (g w) (μ w); let K(w):=xup q (fun b=> lensW p (R w) (μ w) b ((B w).Y b 0))
    have hz: Rose L (fun w=>(X w).re) (fun w=> (p' w+M w*K w).re):=CohX Complex.reCLM (Rose.chain hh (Rose.skip (Eventually.of_forall (fun i=>(mul_add (M i) _ _)))))
    have hl: A/C ≤ ε/4:= by rw [div_le_iff₀ hC]; unfold C; rw [mul_div_cancel₀ _ (show ε/4 ≠ 0 by positivity)]; linarith
    filter_upwards [hz.eventually (ball_mem_nhds (0:ℝ) (show 0 < ε/4 by positivity)), hk,P M' hMp μ hv] with w hx hk hw
    have ht: |(X w).re-(p' w + M w*K w).re| ≤ ε/4:= by simpa [mem_ball,Real.dist_eq] using le_of_lt (show dist _ _< _ from hx)
    have hv: |(p' w).re-landPay G| ≤ ε/4:=le_trans hk (by rwa [sub_sub_self])
    have hh: |(M w*K w).re|≤ ε/4:= le_trans (Complex.abs_re_le_norm _) (hw.trans ((mul_le_mul_of_nonneg_left (H' w|>.2) hB).trans hK))
    rw [Real.dist_eq]; change |(X w).re-landPay G|<_
    rw [Complex.add_re, abs_le] at ht; rw [abs_le] at hv hh; rw [abs_lt]; constructor<;> linarith [ht.1,ht.2,hh.1,hh.2,hv.1,hv.2]
end onset
end YM.Trace.Loft
#print axioms YM.Trace.Loft.awake
