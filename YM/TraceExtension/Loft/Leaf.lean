import YM.TraceExtension.Loft.Stark
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W:Type}{g:W→ Side}{L: Filter W}{G:Gauge}{U:Skuta W G}{V:Jar G}{p:Clip}{R:W→PathData G}{k m n:ℕ}{σ ε A α A' C D a C':ℝ}{B:(w:W)→Dart G (g w)}{ε':W→ℝ}
variable (q:G.ColorIndex)(h:Cred g p R U V σ ε A C D)(ht:Scene g B p R a C' ε')(Q:Tendsto (fun w=>(g w).val) L atTop)(hq:Tendsto ε' L (𝓝 0))(hM:Flare g R p α A')(he:G.Simple)
section fees
include h ht Q hq hM he
lemma LowPay (d i b:Axis): ∃ C:ℝ, 0 ≤ C ∧ ∀ (δ:ℝ), 0 < δ→ δ ≤ 1 →
    ∀ᶠ w in L, ‖Lamp.cob d i q (lensW p (R w) δ b ((B w).Y b 0))‖≤ C*δ⁻¹:=by
    obtain ⟨hf,hh⟩:= vista h; obtain ⟨hv,hG⟩:=onsite Q ht hM hq he b
    obtain ⟨A,hA,H⟩:= cob_hou hv hf Q d i q; obtain ⟨E,hE,M⟩:=cob_hou hG hh Q d i q
    refine ⟨A+E,by positivity,fun δ hd hhμ=>?_⟩; let μ (i:W) := δ; have hm(i): δ≤μ i ∧ μ i≤1:=⟨le_rfl,hhμ⟩; obtain ⟨x,C',B',hx,hC,hB',H'⟩:= blizzard h.live h.hat h.ac h.cb h.σp h.εp hd (μ:=μ) hm
    let F(w):=Border (U.useJar V) w; let V(w):= zell p (R w) (μ w) (g w); let S(w):= wentG G (μ w) (g w)
    have hμ(w):=hd.trans_le (hm w|>.1)
    have hp(w): Ticket (summitM (F w) (μ w)).back (V w):= Ticket.back (alp_m (μ:=μ w) (h.leg w)) ((hM.posit hμ w).det_pos.ne'.isUnit)
    have hl(w): Ticket (cinder G (μ w)).back (S w):= Ticket.back crumb ((ammo_safe _ (hμ w)).det_pos.ne'.isUnit)
    have H1:= H δ hd hhμ _ _ hx (fun i=> (H' i|>.2.2.1).back (H' i|>.1) hx) V hp; have H2:= M δ hd hhμ _ _ hx (fun i=>(H' i|>.2.2.2).back (H' i|>.2.1) hx) S hl
    filter_upwards[H1,H2] with w h1 h2
    obtain ⟨a,X,h,h',HX⟩:=hv.jets.top; obtain ⟨c,L,hc,hL,K⟩:=hG.jets.top
    unfold lensW; rw[cob_plus d i q (sequester (hp w|>.finance) (fun i j=> HX w i j|>.1)) (sequester (hl w|>.finance) (fun i j=> (K w i j).1)),add_mul]; exact (norm_add_le ..).trans (add_le_add h1 h2)
lemma smooth_u (d i b:Axis)(hα:0 < α): Tendsto (fun w=> Lamp.cob d i q (lush ((B w).Y b 0) ∘ input G (g w))) L (𝓝 0):=by
    let F(w):= Lamp.cob d i q (lush ((B w).Y b 0) ∘ input G (g w)); obtain ⟨C,hC,H⟩:=LowPay q h ht Q hq hM he d i b
    rw[Metric.tendsto_nhds]; intro ε hε
    let μ:= min 1 (ε/2/(C+1)); have hL:0<μ:=lt_min zero_lt_one (by positivity); have hm:μ≤1:= min_le_left ..
    let Z(w):= (μ:ℂ)^(2:ℕ)*Lamp.cob d i q (lensW p (R w) μ b ((B w).Y b 0)); have hx:Rose L F Z:= fawn d i b q Q he ht hM hα hL hq
    have hv: 0 < C+1:=by positivity
    have hp := (le_div_iff₀ hv).1 (show μ≤ ε/2/(C+1) from min_le_right ..)
    filter_upwards [hx.eventually (ball_mem_nhds (0:ℂ) (half_pos hε)),H μ hL hm] with w hw hy
    have ht: ‖F w-Z w‖< ε/2:=by simpa [Metric.mem_ball] using hw
    have hz: ‖Z w‖ ≤ ε/2:=by unfold Z; rw[norm_mul,norm_pow,Complex.norm_real, Real.norm_of_nonneg hL.le]; refine (mul_le_mul_of_nonneg_left hy (sq_nonneg _)).trans (?_); rw[show μ^2*(C*μ⁻¹)=μ*C by field_simp]; linarith
    change dist (F w) 0< _; rw[dist_zero_right, ← sub_add_cancel (F w) (Z w)]; linarith only[ht,hz,norm_add_le (F w-Z w) (Z w)]
end fees
abbrev floft (d i:Axis)(q:G.ColorIndex){f:Side}(F: Maze G f):ℂ:= neap 2 (molt 0 ![mood G i q,mood G i q] F) 0 (![step d,-step d]:Land)
def Holt (q:G.ColorIndex){f:Side}(X:Axis→ Maze G f): ℂ:= crest q X - (1/2:ℂ)*suite (fun d i=> floft d i q (X i))
abbrev midPay (q:G.ColorIndex){f:Side}(A:Dart G f):= (Holt q (fun b=>lush (A.Y b 0) ∘ input G f)).re
-- mid in eventual extraction
lemma midAwake (h:Cred g p R U V σ ε A C D)(hS:Scene g B p R a C' ε')(Q:Tendsto (fun w=>(g w).val) L atTop)(h':0<α)(hq:Tendsto ε' L (𝓝 0))(hM:Flare g R p α A')(he:G.Simple): Tendsto (fun w=> midPay q (B w)) L (𝓝 (landPay G)):=by
   let X(w)(b):= lush ((B w).Y b 0) ∘ input G (g w)
   have hu(i):Pico (fun w=>(0:Site (g w))) (fun w=>X w i) 2:=by
       obtain ⟨T,hT,H⟩:=pipe_w G 3
       let c:=a/5/4/5; have hp:=hS.vp; have hc:=hS.c0; have hx:0 < c:=by unfold c; positivity
       refine ⟨c,T*C'*↑(Fintype.card (Loc G 1))*countCost c,hx,(mul_nonneg (mul_nonneg (mul_nonneg hT hc) (by positivity)) ((count_pos hx).le)),fun w=>?_⟩
       have hz:= (hS.house w).sound.palm i 0; apply pet_lush _ (tidal_pay _ hz.1 ?_) hx (by positivity)
       intro v; have hv := H (g w) ((B w).Y i 0) (0:Site (g w)) _ _ (show 0 ≤ a/5 from by positivity) hc hz.1 (fun j=> pea_rain hz ((hS.house w).Y i _) hc hp.le j) v; rwa[show a/5/((↑(3:ℕ):ℝ)+1)/((↑(3:ℕ):ℝ)+2)=c by unfold c; norm_num] at hv
   have ht(d i):Tendsto (fun w=> floft d i q (X w i)) L (𝓝 0):= Rose.alight (Rose.side (cog_neap d i q Q _ (hu i))) (smooth_u q h hS Q hq hM he d i i h')
   have hW: Tendsto (fun w=> (1/2:ℂ)*suite fun d i=> floft d i q (X w i)) L (𝓝 0):=by
       apply Rose.alight (Rose.chain (roseRate (1/2:ℂ) (suite_hold (H:=fun _ _ _=>0) (F:=fun w d i=>floft d i q (X w i)) (fun i j=>by unfold Rose; rw[show (fun _:W=> (0:ℂ))=0 from rfl,sub_zero]; exact ht i j))) (Rose.skip ?_)) (tendsto_const_nhds (x:=0))
       filter_upwards with i; simp[suite]
   have hv:= (Rose.alight (crest_v q hS Q) (awake q h hS Q hq hM he h')).sub (Complex.continuous_re.continuousAt.tendsto.comp hW); rw[Complex.zero_re,sub_zero] at hv; exact hv
end YM.Trace.Loft
