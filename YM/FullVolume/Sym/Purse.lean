import YM.FullVolume.Sym.Badge

/-! Entry prices after both transition buys. Require STEP and comparisons LBelt.
    no assertions yet shrinking Hℓ widths -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Marlin Empire Time
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
/-!
# Slot W.Paper from real credits post-L. Quantities γ times along normals. require arbitrary small α_
   Schedules on spine at pre-exponent. Drives strong Sec and lipschitz motion.
 -/
open FullVolume.Ray Residual Averaging Progress.DirectedRecipe Time Ovens
open Next.Scheduling.Clock Next.Scheduling.Instrument UVNext.CouplingReset
variable (G:Gauge)(L:Side)(b:ℕ) (P:RG.Stage)
variable {α t h r q:ℝ}{K: Postage}{B:BudgetPoint}
abbrev chores (G:Gauge)(P:RG.Stage)(u x:ℝ):=u*(Time.credit G P*δE x)
abbrev spiceF (G:Gauge)(L:Side)(b:ℕ)(P:RG.Stage)(t x:ℝ):= chores G P (t+2*t) x + Height.away P*Boulevard.gold G L x + Boulevard.gold G L x + Height.away P*(Trio.planks G L b P x *Real.exp (Trio.stout P*Trio.coverTicket b))
-- need t small. kinetic export bounds sharpen arbitrary q constant future users.
def sphere (q s t : ℝ): Prop:= 0<t ∧ 2≤q ∧ 0<s ∧ s ≤1 ∧ ∃ u:ℝ, 0≤u∧ u*t*6 ≤ s ∧ ∀ (G:Gauge) (c:Side)(P:BudgetPoint) (A:ℕ→RegularAddress c) (F:sun→ℕ→ Config G c→ℝ) (v b B:ℝ),q≤v→sanction P A F v B→ (∀ t,Meadow.Budget P A (F t) b) → sanction P A F q (u*b+(1+u)*(q/v)^(301:ℕ)*B)
lemma ball_on {q s r:ℝ}(hq:2≤q)(hs:0<s) (hp:s≤1)(he:0<r) :∃ t:ℝ,0<t∧t≤ r∧sphere q s t:=by
  obtain ⟨u,hu,h⟩:= squeeze 300 q (by linarith)
  let t:= min r (s/(6*(1+u))); have ht:0<t:= lt_min he (by positivity)
  refine ⟨t,ht,min_le_left ..,ht,hq,hs,hp,u,hu,?_,h⟩
  have hp:= mul_le_mul_of_nonneg_left (show t ≤ s/(6*(1+u)) from min_le_right ..) hu
  calc _ ≤ u*(s/(6*(1+u)))*6:= by linarith
       _ ≤ s:= by field_simp; nlinarith
-- contract E cost exactly target q. true stamp post bill. Delay with `s` arbitrarily small.
lemma cool_fire (q:ℝ):∀ᶠ x in atTop,q≤ fire G L x / 4:=by
  have hp:=((tendsto_rpow_atTop (show 0<((1:ℝ)/256) by norm_num)).comp (Work.E09.betaF_growth G L)).eventually_ge_atTop (4*q)
  filter_upwards [hp] with i hi; change _ ≤fire G L i at hi; linarith
lemma cold (p s t : ℝ) {u:ℝ} (hp:0<s) (ht:u*t*6 ≤ s):∀ᶠ x in atTop, u*spiceF G L b P t x+(1+u)*(p/(fire G L x/2))^(301:ℕ)*good_gross G L x ≤ chores G P s x:=by
  let v:= Time.credit G P; let q:= s/2*v
  let c(x):= Boulevard.gold G L x; let A:= Height.away P; let e:= Real.exp (Trio.stout P*Trio.coverTicket b); let y x:=betaF G x L
  let f x:=u*(A*c x+c x+A*(Trio.planks G L b P x*e)) + (1+u)*(p/(fire G L x/2))^(301:ℕ)*good_gross G L x
  have hx: Rate G L (-(23/20)) c:= Rate.power
  have he: Rate G L (-(23/20)) (fun x=> u*(A*c x+c x+A*(Trio.planks G L b P x*e))) := ((((hx.mul_left A).add hx).add (((Trio.skyward G L b P).mul_right _).mul_left _)).mul_left _)
  have hK: Rate G L (-((1:ℝ)/256)) (fun x=> p/(fire G L x/2)):=by
    refine Rate.congr ((Rate.power (a:=-((1:ℝ)/256))).mul_left (2*p)) ?_; filter_upwards [Delay.shift_pos G L] with x hx
    rw [Real.rpow_neg hx.le]; unfold fire; ring
  have H : Rate G L (-(23/20)) f:= Rate.add he (((((hK.pow 301).mul_left _).mul (Rate.power (a:=-(1/4))))).weaken (by norm_num))
  have hv:0<v:=Time.credit_pos ..
  filter_upwards [Sienna.contraction G L (a:=1) (b:=q) (by unfold q; positivity) H (show -(23/20:ℝ)< -(11/10) by norm_num),Delay.shift_pos G L,eventually_gt_atTop (0:ℝ)] with x hx hz hX
  have he : δE (betaF G x L)=betaF G x L ^ (-(11/10):ℝ):= by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hz.le,← Real.rpow_mul hz.le]; norm_num
  have hh : δE (betaF G x L) ≤ δE x:= by
    unfold δE; refine Real.rpow_le_rpow (by unfold Clock.gap; positivity) ?_ (by norm_num)
    have hz : x ≤ betaF G x L:= le_add_of_nonneg_right (Work.E04.shift_nonneg G L)
    exact inv_anti₀ (Real.sqrt_pos.mpr hX) (Real.sqrt_le_sqrt hz)
  rw [one_mul,← he] at hx; have hF:=hx.le.trans (mul_le_mul_of_nonneg_left hh (by unfold q; positivity : 0≤q)); let z:= δE x; have hh:0≤z:= Real.rpow_nonneg (by unfold Clock.gap; positivity) _
  rw [show u* spiceF G L b P t x+_=u*3*t*(v*z)+f x from by unfold spiceF chores f c A v z e; ring]
  change _ ≤ s*(v*z)
  unfold q at hF; change f x≤ s/2*v*z at hF
  nlinarith only [hF,mul_le_mul_of_nonneg_right ht (mul_nonneg hv.le hh)]
lemma show_width {d:ℝ} (hd:0<d)(hs:0<t)(hp:t≤1)(ht: t ≤ d) (α:ℝ) : ∀ᶠ x in atTop, ∀ B:BudgetPoint, Time.Same P B→ B.threshold=Instrument.plain.t x→
     regularNeed G B P.clip P.width P.paths α (chores G P t x) ≤ d*δE x:=by
  have hx:= P.width_pos; let H:= Time.top G P
  filter_upwards [late_cubic (2* H * |α|/ d), eventually_gt_atTop (0:ℝ)] with x hx' hp' B he hB
  have hy : 0 ≤ δE x:= Real.rpow_nonneg (gp hp').le _
  rw [Time.table G P he]; unfold chores; rw [hB,(Time.threshold_aligned x hp').1]
  change 2*H* |α|/ d * _ ≤ δE x at hx'; have hh := mul_le_mul_of_nonneg_right ((Time.authorized G P).2) (mul_nonneg hs.le hy)
  change _+H*_ ≤ _; field_simp at hx'; nlinarith only [hx',hh, mul_le_mul_of_nonneg_right ht hy, mul_nonneg hs.le hy]
variable (A : Time.Forecast K)
lemma reunite {s:ℝ}(hs:0<s)(hp:s≤1) (c α:ℝ) (hc:0≤ c):(∀ᶠ x in atTop,∀ (B:BudgetPoint),Time.Same P B→B.B=cover x→ B.threshold=plain.t x → ∀ β, Next.Scheduling.inBand (x+c) β→ ∃ a κ:ℝ, 2*softNeed G B P.clip P.width P.paths α (chores G P s x)≤ a ∧ Payments.Rates B.B (Real.exp (-Payments.Pairing.kGoal K (x+c) β)) (A.pair.strong (x+c) β) a κ):=by
  let u:= Time.softCeiling G P |α|
  filter_upwards [Time.small_expenses (2*u) c, eventually_gt_atTop (1:ℝ), plain.pitched, ((tendsto_atTop_add_const_right _ c tendsto_id).eventually A.pair.currency)] with x hx hv hp' hP B hB hf h W hW
  let y:=x+c; have ht:=zero_lt_one.trans hv; have hx':0≤δE x:= Real.rpow_nonneg (gp ht).le _
  have hb : 0≤ chores G P s x:= mul_nonneg hs.le (mul_nonneg (Time.credit_pos ..).le hx')
  have hu: chores G P s x ≤ B.threshold^2:= by
    have hd : δE x ≤ gap x ^ (2:ℕ) := (Real.rpow_le_rpow_of_exponent_ge (gp ht) (show gap x ≤ 1 from inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt hv.le)) (by norm_num : (2:ℝ)≤(11:ℝ)/5)).trans_eq (Real.rpow_two _)
    exact (mul_le_of_le_one_left (mul_nonneg (Time.credit_pos ..).le hx') hp).trans ((mul_le_of_le_one_left hx' ((Time.authorized G P).1.trans (by norm_num))).trans (hd.trans (pow_le_pow_left₀ (gp ht).le (h ▸ le_mul_of_one_le_right (gp ht).le hp'.2.2.1) 2)))
  have hX:=mul_le_mul_of_nonneg_left (Time.soft_table G P hB (α:=α) le_rfl hb hu) zero_le_two
  have hy := Nat.ceil_le_ceil (pow_le_pow_left₀ (Real.log_pos hv).le (Real.log_le_log ht (show x≤x+c from le_add_of_nonneg_right hc)) 2)
  rw [hf,h] at hX; refine ⟨A.pair.mild y,_,hX.trans ?_, hP.2 W hW B.B (by rw [hf]; exact hy)⟩ -- cast B issue
  change 2* (u*(1+(cover x:ℝ))^4*plain.t x) ≤ _
  unfold Payments.Pairing.mild; apply le_trans (le_trans (le_of_eq (show 2* (u*(1+(cover x:ℝ))^4 * plain.t x)=2*u*(1+(cover x:ℝ))^4 * plain.t x from by ring)) hx); dsimp only [Forecast.pair]; rw [Real.rpow_zero,pow_zero,mul_one,mul_one]
  exact le_mul_of_one_le_left (Real.rpow_pos_of_pos (gp (by linarith)) _).le (le_max_left ..)
lemma profits (P : Postage) (c d:ℝ) (hp:0<d): ∀ᶠ x in atTop,∀ β, Next.Scheduling.inBand (x+c) β→ Real.exp (-Payments.Pairing.kGoal P (x+c) β) ≤ d * plain.w x:= by
  let p:= P.rate/8; have ht:0<p:=div_pos P.pos (by norm_num)
  have hh := Time.late_force p c ht
  have hQ : Tendsto (fun x=> x+c) atTop atTop:= tendsto_atTop_add_const_right _ c tendsto_id
  have hr : Tendsto (fun x:ℝ=> Real.exp (-p * plain.P (x+c)^(2:ℕ))) atTop (𝓝 0):= by
    refine Real.tendsto_exp_atBot.comp ?_
    have hx : Tendsto (fun x=> plain.P x) atTop atTop:= Clock.growing (d:=plain.center) (by unfold Instrument.plain; norm_num) -- name
    exact (((tendsto_pow_atTop (n:=2) (by omega : 2≠0)).comp (hx.comp hQ)).const_mul_atTop_of_neg (by linarith)) -- name
  filter_upwards [Time.late_force (p+p) c (by linarith),hQ.eventually (Postage.saved plain p ht),plain.support 2 one_lt_two, just_near c,hr.eventually (ge_mem_nhds hp)] with x hx hz hS hn hK β hβ
  apply le_trans ((hx P (by unfold p; linarith) β hβ).1)
  rw [neg_add,add_mul,Real.exp_add]; apply mul_le_mul (b:=d) hK ?_ (Real.exp_nonneg _) hp.le; exact hz x (hS x (x+c) (same x) hn)
end YM.PhysicalNext.Repeat.Jams
