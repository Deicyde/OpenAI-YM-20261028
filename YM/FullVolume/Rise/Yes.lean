import YM.FullVolume.Rise.Hat
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Tent
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
/-! Timing sustainability with ANY future norm share. Startup rays selected after Round.Run before reference tuning. -/
open WilsonStartup Design Ovens Progress.DirectedRecipe Padded Apse Jams
open Real (exp log)
variable (G : Gauge)
section timing
open WilsonStartup.Timing
lemma pill {p:BudgetPoint}{s:ℝ}(h : Start.Loan p (exp s/2) (Timing.M s) (Timing.M s) (Timing.quota s)): exp (quota s)-1 ≤ 1:= by
  have ht:= (le_mul_of_one_le_left (sub_nonneg.mpr (Real.one_le_exp h.packets.gamma)) (one_le_pow₀ (n:=4) (a:= ((p.B+p.B+1:ℕ):ℝ)) (by simp))).trans h.margin; exact ht
lemma good_loans (A : RG.Stage) (c:ℝ)(hc:0<c):∀ᶠ s in atTop,∀ b : BudgetPoint,b.threshold=Timing.temp s → b.B= Timing.balls s → b.supportExponent=A.supportExponent → Start.Loan b (exp s/2) (Timing.M s) (Timing.M s) (Timing.quota s) ∧ Bid.quote (Timing.M s) (exp (Timing.quota s)-1) ≤ c* Timing.normK s := by
  let T:=log c
  let d:= |T|+3
  filter_upwards [Timing.loan A.supportExponent, Real.tendsto_log_atTop.eventually_ge_atTop (2*d)] with s hv hs b ht hp he
  obtain ⟨hv,-⟩:= hv b ht hp he
  refine ⟨hv,?_⟩
  unfold Bid.quote normK; apply le_trans (mul_le_mul_of_nonneg_left (show exp (exp (quota s)-1)-1≤ exp 1 from (sub_le_self _ zero_le_one).trans (Real.exp_monotone (pill hv))) (Real.exp_nonneg _))
  rw [show c*_=exp T * Timing.normK s from (by unfold T normK; rw [Real.exp_log hc]), normK,← Real.exp_add,← Real.exp_add,Real.exp_le_exp]; have hg:= Real.add_one_le_exp (4/5*(log s)^2); unfold Timing.M
  have hx : 1≤exp ((log s)^2/5):= Real.one_le_exp (by positivity)
  have hu : exp ((log s)^2)=exp ((log s)^2/5)*exp (4/5*(log s)^2):= by rw [← Real.exp_add]; congr 1; ring
  have ha: 3≤d:= le_add_of_nonneg_left (abs_nonneg _)
  have hh: 4/5*(log s)^2 ≥ 1-T:= by unfold d at hs; nlinarith [sq_nonneg (T+1), abs_nonneg T, neg_abs_le T]
  rw [hu]; have hd : 0≤4/5*(log s)^2 := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hg (zero_le_one.trans hx),mul_le_mul_of_nonneg_right hx hd,hh]
lemma affording (A : Stage) (c:ℝ)(hp:0<c): ∀ᶠ s : ℝ in atTop,∀ b : BudgetPoint,
    b.order=A.order → b.power=A.power → b.supportExponent=A.supportExponent → b.threshold=Timing.temp s →
      Start.book G b (2*exp s) ≤ c*normE s := by
  let C := (Fintype.card Signed:ℝ)*Fintype.card PlaqAxes*(exp (A.supportExponent*5^4)*(2*Start.price G A.order A.power))
  have hC : 0<C := by unfold C; have := (Start.constants G A.order A.power).1; positivity
  filter_upwards [Timing.small (ε:=1/40) (by norm_num),eventually_ge_atTop (4*(log C-log c)),eventually_ge_atTop (0:ℝ)] with s h hs h0 b hk hP ha ht
  have hh : Start.book G b (2*exp s) = exp (log C + s + 5*(-(s/2)+(log s)^2)) := by
    simp only [Start.book,Start.item,Start.overhead,ha,hk,hP,ht,Timing.temp]
    rw [Real.exp_add (log C + s), Real.exp_add (log C), Real.exp_log hC,show (5:ℝ)=(↑(5:ℕ):ℝ) by norm_num,Real.exp_nat_mul]; unfold C; push_cast; ring
  rw [hh, normE,show c* exp (-(11/10)*s)= Real.exp (log c+ (-(11/10)*s)) from (by rw [Real.exp_add,Real.exp_log hp]),Real.exp_le_exp]; linarith [sq_nonneg (log s)]
structure Purch (G:Gauge)(a:Levels G)(c:ℝ)(N:ℕ):Prop where
  permits: (a.params N).clip.direct≤1 → Start.Allows a N
  debit:Start.book G (a.budget N) (2*a.clock.hatBeta N)≤ c*a.clock.allowance N
  height:∃ σ κ γ,Start.Loan (a.budget N) (a.clock.hatBeta N/2) σ κ γ ∧ Bid.quote κ (exp γ-1) ≤ c*a.clock.forcedAllowance N
lemma sunsets (A : Stage) (c:ℝ)(hc:0<c):∀ᶠ x in atTop,∀ (a:Levels G) (N:ℕ),a.params N=A → a.clock.hatBeta N=x → Purch G a c N:=by
  have he :∀ᶠ x in atTop,A.clip.direct ≤ 1→∀ (a:Levels G) N,a.params N=A → a.clock.hatBeta N=x→ Start.Allows a N := by
    by_cases h:A.clip.direct≤1; · simpa [h] using Timing.enough G A h
    simp [h]
  filter_upwards [he,Real.tendsto_log_atTop.eventually (good_loans A c hc), Real.tendsto_log_atTop.eventually (affording G A c hc),eventually_gt_atTop (0:ℝ)] with x hx hq h hz a N ha hN
  let b := a.budget N
  have hb : b.B=Timing.balls (log x) := congr_arg Timing.balls (congr_arg log hN)
  have hp : (Real.sqrt x)⁻¹ = exp (-(log x / 2)) := by rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hz]; congr 2; ring
  have ht : b.threshold = Timing.temp (log x) := by
    change (Real.sqrt (a.clock.hatBeta N))⁻¹ * exp _ = _
    unfold Timing.temp; rw [hN,hp,Real.exp_add]
  have he : a.clock.allowance N = normE (log x) := by
    unfold Calendar.allowance Calendar.hatCoupling normE; rw [hN,hp,← Real.exp_mul]; congr 1; ring
  have hw : a.clock.forcedAllowance N = normK (log x) := by
    unfold Calendar.forcedAllowance Calendar.monitor normK; rw [hN,← Real.exp_mul]; congr 3; ring
  have hk : b.order=A.order := congr_arg Stage.order ha; have hP : b.power=A.power := congr_arg Stage.power ha; have hE : b.supportExponent=A.supportExponent := congr_arg Stage.supportExponent ha
  obtain ⟨hq,hv⟩:= hq b ht hb hE; rw [Real.exp_log hz] at hq
  refine ⟨fun h=> hx (ha ▸ h) _ _ ha hN,?_,?_⟩
  · have ht := h b hk hP hE ht; rw [Real.exp_log hz] at ht; rw [hN,he]; exact ht
  rw [hw,hN]; exact ⟨_,_,_,hq,hv⟩
end timing
section syntaxP
variable {G}
open UVNext.CouplingReset Next.Scheduling.Clock PriceCompiler
variable {S:Supply.Sheet G}{K:Rolls S} {Y:Protection K} {c:ℝ}
def Credit (V:Delays Y)(s:ℝ) := ∀ (P:Bar V)(W:Wait P)(a:Levels G)(_ : Paid W a),∀ N,Purch G a s N
lemma quotes (V:Delays Y)(hc:0<c): ∃ Z:Delays Y,DelayLe V Z ∧∀ X:Delays Y,DelayLe Z X→ Credit X c:=by
  -- don't use Level ratio; startup uses profile Z via previous step j. Zero has j=firstOne.
  obtain ⟨x,-,h,hK⟩:= collect_upper V.betaEntry _ (fun j=>sunsets G (S.profile j) c hc)
  refine ⟨{V with betaEntry:=x}, ⟨h,le_rfl,le_rfl,le_rfl⟩,fun U h X W a hp N=>?_⟩
  let j:=a.clock.J N
  have hf:a.params N=S.profile j:=params_eq hp N
  apply hK j (a.clock.hatBeta N) _ a N hf rfl
  apply (show x j ≤ U.betaEntry j from h.beta _).trans
  rcases N with _|N
  · change U.betaEntry (a.clock.J 0)≤_; rw [hp.firstZero,← hp.firstOne]; exact hp.pays _
  have hk:= PriceCompiler.beta_eq hp N
  unfold j; rw [hk]; apply (hp.pays N).trans
  exact le_add_of_nonneg_right (Work.E04.shift_nonneg G _)
end syntaxP
end YM.PhysicalNext.Repeat.Tent
