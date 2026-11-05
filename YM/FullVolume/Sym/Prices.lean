import YM.FullVolume.Sym.Avenues
import YM.FullVolume.C.Songbook

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
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {Q: Targets s K} {Z: Expenses Q}
local notation "ε" => (-(3/8):ℝ)
-- BeforeL monocyte. work with unrestricted beforeL but require actual Stamp.
lemma colorful (P : Teller G) (Q : Target G P)(hQ:Q.rate ≤ -(7/16:ℝ)) (M:RG.Stage) (hp:M.supportExponent+3<Q.exp) :∃ N:ℕ,∀ L:Side,N≤L.val → ∀ (W μ:ℝ),0<W→0<μ→∀ (o:Target.Order G W)(C:ℝ),∀ᶠ x in atTop, ∀ (c f:Side) (S:StepData c f) (T:Tube G S),Works P L x S T → Stamp T → ∀ (R:Rep G f)(H: Cash W x μ L Q o C T R)(U:Tune H (fire G L x) (thaw G L x)) (B:BudgetPoint), B.order=M.order→ B.power=M.power→ B.supportExponent=M.supportExponent → B.threshold=Pressure.temp x → Candy U Chi.canonical (preExponent B) (pottery G L x) B:=by
  obtain ⟨n,hL⟩:= Empire.candidates hQ; refine ⟨n,fun L hl W μ hW hμ o C=>?_⟩
  by_cases he:∃ D:Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · filter_upwards with x c f S T h; exact (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim
  obtain ⟨D,hD,h,d⟩:= he; have hx := hL L hl D hD M.order M.power Chi.canonical W μ hW hμ o C _ (show 0≤M.supportExponent+3 from add_nonneg M.price_pos.le (by norm_num)) hp
  filter_upwards [hx] with x hy c f S T hs hf R H U B h₁ h₂ h₃ hB; unfold preExponent; rw [h₃]; exact hy c f S T (hs.patch h d) hf R H U B h₂ hB h₁
variable (G) (L:Side) (b:ℕ) (σ:RG.Stage)
-- fixed rate before ensemble
abbrev wind (G:Gauge) (L:Side)(σ:RG.Stage)(x:ℝ):= Height.away σ*(pottery G L x+ 4* betaF G x L^(-(7/16):ℝ))
abbrev brimP (G:Gauge) (L:Side)(b:ℕ)(σ:RG.Stage)(x:ℝ)(i:Stars):=2*((Fintype.card (Site (Trio.fence b (radiusB x) i)):ℝ)*(wind G L σ x))
abbrev baseP (G:Gauge)(L:Side)(b:ℕ)(σ:RG.Stage)(x:ℝ):= (ballCost (Meadow.studio b (radiusB x)):ℝ)*wind G L σ x
def days (σ:RG.Stage): BudgetPoint:= ⟨σ.power,σ.order,σ.supportExponent,1,1,σ.power_ge,σ.order_ge,σ.price_pos,by norm_num,zero_lt_one,le_rfl⟩
local notation "B'"=> Trio.base b
section apricot
local notation "P"=> days σ
local notation "T" => Trio.coverTicket b
def potP (x:ℝ):= Marlin.tithe (2*Trio.base b (radiusB x)) (grail (Meadow.studio b (radiusB x)) (Trio.fence b (radiusB x)) (fun _=>baseP G L b σ x) (wind G L σ x)) (days σ) (Trio.coverTicket b)
def abundantP (x:ℝ):= torusP (days σ) (brimP G L b σ x) (Trio.base b (radiusB x)) (Trio.coverTicket b) (wind G L σ x)
lemma wind_bills : Rate G L ε (wind G L σ):= ((Rate.power).add ((Rate.power (a:=(-(7/16):ℝ))).mul_left 4|>.weaken (by norm_num))).mul_left _
lemma pot_bills : Rate G L ε (potP G L b σ):= by
  have hz:= Trio.rows G L b; have hb:= Trio.balls G L hz.1
  have he: Rate G L ε (baseP G L b σ):= by simpa only [zero_add] using! hb.mul (wind_bills G L σ)
  have hW: Rate G L ε (fun x=>lightTax (Trio.fence b (radiusB x)) (fun _=>baseP G L b σ x)):= by
    unfold lightTax; apply Trio.sparks G L (f:=fun i x=> |Slide.ray i| * _); intro i; simpa only [zero_add] using! (((Trio.feeStars G L b i).mul (he.add he)).mul_left |Slide.ray i|)
  have ht:= (Trio.balls G L hz.2.2.2).mul (((he.mul_left 2).add hW).mul_left 2)
  rw [zero_add] at ht; exact ht.mul_right (Real.exp (((P).supportExponent+1+1)*T))
lemma abundant_bills : Rate G L ε (abundantP G L b σ):= by
  have hz:= Trio.rows G L b; have hb i : Rate G L ε (fun x=> brimP G L b σ x i):=by simpa only [zero_add] using! (((Trio.feeStars G L b i).mul (wind_bills G L σ)).mul_left 2)
  have hV: Rate G L ε (fun x=> Trio.oroW P (Trio.base b (radiusB x)) (brimP G L b σ x)):=by
    apply Trio.sparks G L (f:=fun i x=>|Slide.ray i| * _); intro i
    have he:Rate G L 0 (fun x=> Trio.tilt P (B' (radiusB x))):=by
      simpa only [zero_mul] using! ((((Rate.const 1).add (hz.2.2.1).uses).pow ((P).power*(P).order)).mul_left ((2:ℝ)^(P).order))
    simpa only [zero_add] using! ((he.mul (hb i)).mul_left |Slide.ray i|)
  exact (wind_bills G L σ).add ((hV.mul_right _).mul_left _)
lemma popcorn {J:Teller G}(Q:Target G J) (F:Postage) (A:Time.Forecast F) {μ:ℝ} (hf:A.hard ≤ μ/16):∀ᶠ x in atTop,∀ β,Next.Scheduling.inBand (betaF G x L) β→∃ κ, Payments.Rates (radiusB x) (A.pair.strong (betaF G x L) β) (Tune.softW Q L μ x) (potP G L b σ x) κ:=by
  have hΩ:0<A.hard:= F.pos.trans A.surplus; have hμ :0<μ:= by linarith
  filter_upwards [eventual_resize J (stella Q) L μ hμ 0 F A hf (1/16) (by norm_num),Marlin.pricingBuy G L F A,(pot_bills G L b σ) _ (show ε < -(1/8:ℝ) by norm_num), Delay.shift_pos G L] with x hx hy hp ht β hβ
  apply hy _ hβ _ _ -- nonnegative arm & pot
  · change 0 ≤ Tune.softW Q L μ x; unfold Tune.softW Tune.prismD Target.mergeScale; have ht : 0<(stella Q).overture L μ x 0 := stella Q|>.overture_pos _ _ ht; positivity -- arity
  · have hb : 0≤ wind G L σ x:=by have hb : turnFee (days σ)=Height.away σ:=rfl; have h : 0<Height.away σ:= hb ▸ turnFee_pos _; unfold wind pottery; positivity
    have hV:0≤ baseP G L b σ x:= mul_nonneg (by positivity) (hb); unfold potP Marlin.tithe; unfold grail lightTax; have hx:0≤ lightTax (Trio.fence b (radiusB x)) (fun _=>baseP G L b σ x):= Finset.sum_nonneg fun _ _=> mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (add_nonneg hV hV)); change 0 ≤ _*(2*(2*_+ lightTax _ _))*_; positivity
  · have ht':Tune.softW Q L μ x= 2*Cash.armK (stella Q) L μ x 0 0:= by unfold Tune.softW Tune.prismD Cash.armK; rw [pow_zero,inv_one]; ring
    rw [ht']; refine le_trans (mul_le_mul_of_nonneg_left (hx _ hβ) zero_le_two) (le_of_eq ?_); ring
  exact (le_abs_self _).trans hp
end apricot
-- store LI Need & actual pays. Frontier able to swap S.K flags -/
variable {G} {J:Teller G}
def ArcReady (Q:Target G J) (M:RG.Stage) (L:Side) := ∀ (W μ:ℝ), 0<W→0<μ→∀ (o:Target.Order G W) (C:ℝ),∀ᶠ x in atTop, ∀ (c f:Side) (S:StepData c f)(T:Tube G S), Works J L x S T → Stamp T → ∀ (R:Rep G f)(H:Cash W x μ L Q o C T R)(U:Tune H (fire G L x) (thaw G L x))(B:BudgetPoint), B.order=M.order→B.power=M.power→ B.supportExponent=M.supportExponent→B.threshold=Pressure.temp x→Candy U Chi.canonical (preExponent B) (pottery G L x) B
variable {D:Rolls s} {Θ:Protection D} {w:Return.Wages} {E:ℕ→ℝ}(R : Register D Z w E) {F:ℕ→ℕ→ Postage}{S:Time.Scouts (F:=F)}
def Demand (Q:Targets s K) (D: Rolls s):=∀ i j,StepStages j i→ArcReady (Q j i) (s.profile i) (D.L j)
variable {i j:ℕ}
-- ledger super-W can Ψ β shrink independent of all N,m years
local notation "K'"=> (s.profile i)
def good_gross (G:Gauge)(L:Side)(x:ℝ):= betaF G x L^ (-(1/4):ℝ)
structure Slot (i j:ℕ) (x:ℝ)(S:Time.Scouts (F:=F)):Prop where
    aura : ∀ (c f:Side)(P:StepData c f)(T:Tube G P), Works (Testing.query s K j i) (D.L j) x P T → Stamp T→ ∀ (V:Rep G f)(H: Cash (w j i) x (R.μ j i) (D.L j) (Q j i) (R.o j i) (R.c j i) T V)(U:Tune H (fire G (D.L j) x) (thaw G (D.L j) x))(B:BudgetPoint), B.order=(s.profile i).order→ B.power=(s.profile i).power→ B.supportExponent=(s.profile i).supportExponent→ B.threshold=Pressure.temp x→ Candy U Chi.canonical (preExponent B) (pottery G (D.L j) x) B
    height : 4≤fire G (D.L j) x
    pace : abundantP G (D.L j) (Q j i).halo (s.profile i) x ≤ good_gross G (D.L j) x
    firm : ∀ β,Next.Scheduling.inBand (betaF G x (D.L j)) β→ ∃ κ, Payments.Rates (radiusB x) ((S j i).pair.strong (betaF G x (D.L j)) β) (Tune.softW (Q j i) (D.L j) (R.μ j i) x) (potP G (D.L j) (Q j i).halo (s.profile i) x) κ
lemma slots_eventually (h: Demand Q D) (hp: Pocket R S) (ht : StepStages j i): ∀ᶠ x in atTop, Slot R i j x S:= by
  have he:= R.consumes j i ht; filter_upwards [h i j ht (w j i) (R.μ j i) he.1 he.2.1 (R.o j i) (R.c j i), (abundant_bills G (D.L j) (Q j i|>.halo) (s.profile i)) _ (show ε< -(1/4:ℝ) by norm_num),popcorn G (D.L j) _ _ (Q j i) (F j i) (S j i) (μ:=R.μ j i) ((hp.price _ _ ht).trans (by have h:= he.2.1; linarith)), ((tendsto_rpow_atTop (show 0 < ((1:ℝ)/256) by norm_num)).comp (Work.E09.betaF_growth G (D.L j))).eventually_ge_atTop _ ] with x hx hv hu hz
  exact ⟨hx,hz,(le_abs_self _).trans hv,hu⟩
def Degree (S : Time.Scouts (F:=F))(V:Delays Θ):Prop:=∀ j x,V.betaEntry j ≤ x→∀ i,StepStages j i→ Slot R i j x S -- R inclusion
lemma degrees (V: Delays Θ)(h: Demand Q D)(hp:Pocket R S):∃ U: Delays Θ,DelayLe V U∧∀ W:Delays Θ, DelayLe U W→ Degree R S W := by
  obtain ⟨x,-,hx,hS⟩:= collect_upper V.betaEntry _ fun j=> eventually_transitions j _ _ fun i h' => slots_eventually R h hp h'
  exact ⟨{V with betaEntry:=x}, ⟨hx,le_rfl,le_rfl, le_rfl⟩, fun W H j y hu=> hS j y ((H.beta j).trans hu)⟩
lemma requirements (Q:Targets s K) (hp:∀ j i, (s.profile i).supportExponent+3<(Q j i).exp) (ht:∀ i j, (Q i j).rate ≤ -(7/16)): ∃ x:ℕ→ℕ, ∀ j i, StepStages j i→∀ L:Side,x j≤L.val→ArcReady (Q j i) (s.profile i) L:=by
  choose u hx using fun j i=> colorful (Testing.query s K j i) (Q j i) (ht j i) (s.profile i) (hp j i)
  exact ⟨fromMax u,fun j i h L he=> hx j i L ((le_fromMax u h).trans he)⟩
end YM.PhysicalNext.Repeat.Jams
