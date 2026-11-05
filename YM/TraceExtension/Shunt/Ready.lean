import YM.TraceExtension.Shunt.Cavity
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shunt
open RG Wilson Lattice Source Labels Finset Push.Local Next.Foundations MergeProof Planned.GuardedAtom Guard Extra.Histories Filter Function Relay Det
open MeasureTheory
open Pressure Stationary AnalyticBridge VerifiedReset Perfect Turret Shepherd Filch Fen Kits Pills Loft Xo Zn Swift Wicket Weir Push.Uniform StressFlux
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{F:Labels.Frame G 5}{n:Side} {T:SectionData F}{H:Hol G}{R:Rep G n}{x a b c d:ℝ}
-- stage clocks.Section permissions. Keep w spire calibr.Capture o flux.
lemma norm_witL(K:ℝ)(h:0≤K):∀ᶠ x:ℝ in atTop,K*swole x ≤ Weir.crumb x:=by
    let f(x:ℝ):= K*x^(-(1/100:ℝ))*Wave 2 x; have hz:Lim (0+-(1/100:ℝ)+0) f:= ((board h).prod (sands (-(1/100:ℝ)))).prod (ferry (waveM 2)); filter_upwards [hz.tiny (by norm_num)] with x hx; unfold swole Weir.crumb; rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); apply le_of_mul_le_mul_right (a:=Wave 2 x) ?_ (Zn.wake ..); change _ ≤ Wave (-2) x*Wave 2 x; exact hx.trans (le_of_eq (by rw[Zn.walt]; simp[Wave]))
abbrev stepX(x:ℝ):= thetaP x^ (2:ℕ)*Wave (-1) x
lemma staxy (K:ℝ)(h:0 ≤ K):∀ᶠ x:ℝ in atTop,K*crumb x ≤ stepX x:=by
    filter_upwards [((waveM (-2)).times K h) (-1) (by norm_num)] with x hx; unfold Weir.crumb; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hx.2 (sq_nonneg _)
-- unit metric + polar Cart.Mid object
structure Combat (T:SectionData F)(H:Hol G)(R:Rep G n)(x:ℝ)(J:Dart G n)(U:Finset GreenA)(P L:Finset ℕ)(k q:ℕ)(b:Axis)(X: Coefficient F n) :Prop where
   charge : Proxy T H R (tower (Cleft x q)) X (filmR (composedZ R x J k q U P L b)) (Weir.smoke x) (grantS x) (grantS x)
   stick : X.x=tuneD U P L x R J k q H F b
   money : F.coeffSize (addUp R x J k q U P L H F b)≤ Weir.crumb x
   phase : F.coeffSize (altoD R x H F (relic R J x U b)) ≤ stepX x
   lower : F.coeffSize (altoD R x H F (kerr x k (YCore x J b) (ochre R x U P))) ≤ stepX x
   march : F.coeffSize (altoD R x H F (swellW R P x (YCore x J) b)) ≤ stepX x
lemma trendH (G:Gauge)(S:Stage)(F:Labels.Frame G 5)(C:SectionData F)(H:Hol G)(k d:ℕ)(p:ℝ)(hp:0 ≤ p):∀ᶠ x:ℝ in atTop,∀ (q:ℕ),1100≤q→ q≤ towerH x d→∀ (n:Side) (Λ:ℝ)(R:Rep G n)(J:Dart G n),
    ToolF k q (Cleft x q) x (peace x) R→Readable H C R.p n p→C.footprint (0:Site n)⊆tempQ x→ Age S x Λ R→ Wealth S R x J→∀ (U:Finset GreenA)(P L:Finset ℕ)(b:Axis), Merch R x J U P k→Depot R x (shelves n U P L) q k (YCore x J b) (ochre R x U P) (swole x)→∃ X,Combat C H R x J U P L k q b X:=by
    let r:= readPrice H F; let v:=atomPrice H F p; let K:=(1+p)*r+v; let A:= Real.exp (S.supportExponent*TileNo)
    have hv: 0 ≤ v:=zero_le_one.trans (atomPrice_ge_one _ _ hp); have hr:0≤ r:=zero_le_one.trans (readPrice_pos ..); have ha:0≤ A:= (Real.exp_pos _).le; have ht:r+v≤ K:= add_le_add_left (le_mul_of_one_le_left hr (le_add_of_nonneg_right hp)) _;have hh:0≤ K:= (add_nonneg hr hv).trans ht
    filter_upwards [norm_witL K hh,norm_witL 1 zero_le_one,staxy r hr, ((waveM ((1:ℝ)/8)).times ((4*A+1)*K) (by positivity)) (1/6) (by norm_num), eventually_gt_atTop (1:ℝ)] with x hx hh' hD hw h q hq hq' n Λ R J ht' hP hX H' H₁ U P L b hr' hp'
    let F' := C; have he:0≤ trayF x:= mul_nonneg (sq_nonneg _) (Zn.wake ..).le; have hp:0 ≤ swole x:= by unfold swole; positivity;
    have hF:0≤ Weir.crumb x:= mul_nonneg (sq_nonneg _) (Zn.wake ..).le; have hK:crumb x ≤ trayF x:= mul_le_mul_of_nonneg_left (Zn.wane x (by norm_num : (-(2:ℝ))≤1/8)) (sq_nonneg _); let t:=2*crumb x+2*trayF x
    obtain ⟨X,hC,hY,hL⟩:= duetM p k 0 q x Λ U P L b R ht' hP hX H' hr' H₁ hp'
    have hz := show ((R.p.mass (tempQ x (n:=n)) t+swole x)*K≤ grantS x) from ?_; have hV(P: Peat G n)(hp:Snow R P x (crumb x)):F.coeffSize (altoD R x H F P) ≤ stepX x:= (weighted_bound H F _ (Real_regular hp.regular) hP.order hP.power (Real_salary hp.regular hp.fare)).trans hD
    refine ⟨X,hC.wide ((mul_le_mul_of_nonneg_left ht (show 0 ≤ R.p.mass (tempQ x (n:=n)) t+swole x by unfold BudgetPoint.mass t; positivity)).trans hz) hz (fun _ h=>h),hY,hL.trans ((mul_le_mul_of_nonneg_right ht hp).trans hx),hV _ (hr'.relicC _),hV _ (hr'.tune _),hV _ (hr'.lones _|>.puff)⟩
    have hD: (R.p.mass (tempQ x (n:=n)) t) ≤ A*(4*trayF x):=by
        have ht': t ≤ 4*trayF x:=by unfold t; linarith only[hK]
        apply mul_le_mul _ ht' (show 0≤t by unfold t; positivity) ha; apply Real.exp_monotone; rw[H'.depth]; gcongr; exacts [S.price_pos.le, tote S x Λ R H']
    have hy: swole x ≤ trayF x:=le_trans (by simpa only[one_mul] using hh') hK; apply (mul_le_mul_of_nonneg_right (add_le_add hD hy) hh).trans; change _ ≤ thetaP x^(2:ℕ)*Wave (1/6) x; refine le_trans (le_of_eq (b:=thetaP x^(2:ℕ)*((4*A+1)*K*Wave (1/8) x)) ?_) (mul_le_mul_of_nonneg_left hw.2 (sq_nonneg _)); unfold trayF; ring
end YM.Trace.Shunt
#print axioms YM.Trace.Shunt.trendH
