import YM.TraceExtension.Loft.Steps
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W:Type}{g:W→ Side}{L: Filter W}{G:Gauge}{U:Skuta W G}{V:Jar G}{p:Clip}{R:W→PathData G}{k m n:ℕ}{σ ε A α A' C D a C':ℝ}{B:(w:W)→Dart G (g w)}{ε':W→ℝ}
variable (q:G.ColorIndex)(h:Cred g p R U V σ ε A C D)(ht:Scene g B p R a C' ε')(Q:Tendsto (fun w=>(g w).val) L atTop)(hq:Tendsto ε' L (𝓝 0))(hM:Flare g R p α A')(he:G.Simple)
section fees
include h ht Q hq hM he
lemma approxim (d i b:Axis): ∃ C:ℝ, 0 ≤ C ∧ ∀ (δ:ℝ), 0 < δ→ ∀ (μ: W→ℝ), (∀ w,δ ≤ μ w ∧ μ w≤1)→
    ∀ᶠ w in L, ‖lux d i q b (lensW p (R w) (μ w) b ((B w).Y b 0))‖≤ C* (μ w)⁻¹:=by
    obtain ⟨hf,hh⟩:= vista h; obtain ⟨hv,hG⟩:=onsite Q ht hM hq he b
    obtain ⟨A,hA,H⟩:= arc_y hv hf Q d i b q; obtain ⟨E,hE,W⟩:=arc_y hG hh Q d i b q
    refine ⟨A+E,by positivity,fun δ hd μ hm=>?_⟩; obtain ⟨x,C',B',hx,hC,hB',H'⟩:= blizzard h.live h.hat h.ac h.cb h.σp h.εp hd (μ:=μ) hm
    let F(w):=Border (U.useJar V) w; let V(w):= zell p (R w) (μ w) (g w); let S(w):= wentG G (μ w) (g w)
    have hμ(w):=hd.trans_le (hm w|>.1)
    have hp(w): Ticket (summitM (F w) (μ w)).back (V w):= Ticket.back (alp_m (μ:=μ w) (h.leg w)) ((hM.posit hμ w).det_pos.ne'.isUnit)
    have hl(w): Ticket (cinder G (μ w)).back (S w):= Ticket.back crumb ((ammo_safe _ (hμ w)).det_pos.ne'.isUnit)
    have H1:= H δ hd μ hm _ _ hx (fun i=> (H' i|>.2.2.1).back (H' i|>.1) hx) V hp; have H2:= W δ hd μ hm _ _ hx (fun i=>(H' i|>.2.2.2).back (H' i|>.2.1) hx) S hl
    filter_upwards[H1,H2] with w h1 h2
    obtain ⟨a,X,h,h',HX⟩:=hv.jets.top; obtain ⟨c,L,hc,hL,K⟩:=hG.jets.top
    unfold lensW; rw[lux_a d i b q (sequester (hp w|>.finance) (fun i j=> HX w i j|>.1)) (sequester (hl w|>.finance) (fun i j=> (K w i j).1)),add_mul]; exact (norm_add_le ..).trans (add_le_add h1 h2)
lemma reprise : ∃ C:ℝ,0 ≤ C∧ ∀ (δ:ℝ),0<δ →∀ (μ:W→ℝ), (∀ w,δ≤ μ w∧ μ w≤1) → ∀ᶠ w in L, ‖(μ w:ℂ)^ (2:ℕ)*xup q (fun b=>lensW p (R w) (μ w) b ((B w).Y b 0))‖ ≤ C*μ w :=by
   choose C hC H using approxim q h ht Q hq hM he; let K:=∑ i,∑ j,∑ k,C i j k; refine ⟨K,sum_nonneg (fun i _=> sum_nonneg fun j _=>sum_nonneg fun k _=>hC ..),fun δ hd μ hx=>?_⟩
   filter_upwards [eventually_all.mpr fun d=>eventually_all.mpr fun i=> eventually_all.mpr fun b=> H d i b δ hd μ hx] with w hw
   let f(b):= lensW p (R w) (μ w) b ((B w).Y b 0); have he(i j:Axis): ‖fata i j q f‖ ≤ (∑ b,C i j b)*(μ w)⁻¹:= by rw[sum_mul]; exact (norm_sum_le ..).trans (sum_le_sum fun k _=>hw i j k)
   have hp:= hd.trans_le (hx w|>.1)
   have hv: ‖xup q f‖ ≤ K*(μ w)⁻¹:=by
      unfold K xup; rw [sum_mul]; apply (norm_sum_le ..).trans; refine sum_le_sum (fun i _=>?_); rw [sum_mul]; apply (norm_sum_le ..).trans; refine sum_le_sum (fun j _=>?_); by_cases h:i=j
      · rw[if_pos h,norm_zero]; exact mul_nonneg (sum_nonneg (fun k _=>hC ..)) (inv_nonneg.mpr hp.le)
      rw[if_neg h]; exact he i j
   rw[norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hp.le]; apply (mul_le_mul_of_nonneg_left hv (sq_nonneg _)).trans_eq;field_simp
end fees
end YM.Trace.Loft
