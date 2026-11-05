import YM.FullVolume.Florid.Gild
import YM.FullVolume.Florid.Suns
import YM.FullVolume.Sym.Shorn
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
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
open ConnectedActivityE6.Empire.Imago Crew Mallow Extra.Iteration Ovens Ovens.Pipes Progress.DirectedRecipe Rack FullVolume.Ray.Weigh
variable {G:Gauge}{s:Sheet G} {K:MapPrices} {Q:Targets s K}
open Testing Push.PriceCompiler Org
open Time Next.Scheduling.Clock Next.Scheduling.Instrument
structure Plum (G:Gauge) (P:Teller G)(Q:Target G P)(M:RG.Stage)(L:Side)(x:ℝ)(a W μ:ℝ)(o:Target.Order G W)(C t:ℝ) : Prop where
    single : ∀ (c f:Side)(S:StepData c f)(T:Tube G S),Works P L x S T→ Stamp T→∀ (R:Rep G f)(H:Cash W x μ L Q o C T R)(U:Tune H (fire G L x) (thaw G L x))(B:BudgetPoint),B.power=M.power→B.order=M.order→B.supportExponent=M.supportExponent→ B.threshold=Pressure.temp x→
     Mill.Jam H U B Chi.canonical (M.supportExponent+2) (pottery G L x) ∧ ∀ (A:Type)[Fintype A](V:A→ Mill U) Cy, Crew.Pave V Cy → Crew.Wield Chi.canonical V Cy (M.supportExponent+2) (pottery G L x) (Real.exp (-Q.mark L μ x))
    shiftT : ∀ p:ℝ,0≤p → p ≤ potP G L Q.halo M x→ ∃ κ,Payments.Rates (radiusB x) (Mallow.stems μ L G x) (Real.exp (-Q.mark L μ x)) p κ
    later : ∀ (B:BudgetPoint),Time.Same M B→B.B=radiusB x→B.threshold=Pressure.temp x→ let f:=softNeed G B M.clip M.width M.paths a (chores G M t x);0≤2*f →∃ κ, Payments.Rates (radiusB x) (straw μ L G x) (Mallow.stems μ L G x) (2*f) κ
-- clock sales t varies ≤1.Calendar
set_option maxHeartbeats 800000 in
private lemma crisp (G:Gauge)(M:RG.Stage)(L:Side)(p:ℝ) (t:ℝ)(hp:0<t)(hv:t ≤1):∀ᶠ x in atTop,∀ (B:BudgetPoint),Time.Same M B→B.B=radiusB x→B.threshold=Pressure.temp x→ softNeed G B M.clip M.width M.paths p (chores G M t x) ≤ betaF G x L ^ (-(1/4):ℝ):=by
  -- cf Mallow.offerS. reweight.
  let c:=G.slopeConstant*Real.log L.val
  filter_upwards [Time.small_expenses (Time.softCeiling G M |p|) c, plain.pitched, Delay.shift_pos G L,eventually_gt_atTop (1:ℝ)] with x hx hz hF hw B hf hB hT
  have ht : plain.t x=B.threshold:= by rw [hT,(Time.threshold_aligned x (by linarith)).1]; rfl
  have hh:B.B=cover x:=hB; have hg:0<gap x:= gp (by linarith)
  have he:= mul_nonneg (Time.credit_pos G M).le (Real.rpow_nonneg hg.le (11/5:ℝ)); let f:= chores G M t x
  have hS : gap x ≤ 1:= inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt hw.le); have hc:0 ≤ f:= mul_nonneg hp.le he
  have hA : credit G M * δE x ≤ B.threshold^2:=by
    have hd : δE x ≤ gap x ^ (2:ℕ) := (Real.rpow_le_rpow_of_exponent_ge hg hS (by norm_num : (2:ℝ)≤(11:ℝ)/5)).trans_eq (Real.rpow_two _)
    have hy := mul_le_of_le_one_left (b:=δE x) (Real.rpow_nonneg hg.le _) ((Time.authorized G M).1.trans (by norm_num)); exact hy.trans (hd.trans (pow_le_pow_left₀ hg.le (ht ▸ le_mul_of_one_le_right hg.le hz.2.2.1) 2))
  refine (Time.soft_table G M hf le_rfl hc ((mul_le_of_le_one_left he hv).trans hA)).trans ((show softCeiling G M |p| *(1+(B.B:ℝ))^4 * B.threshold ≤ gap (betaF G x L)^ ((1:ℝ)/2) from by rw [hh,← ht]; exact hx).trans_eq ?_); unfold gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hF.le,← Real.rpow_mul hF.le]; ring_nf
-- supply ANY d.Q not Burn.F. Cost consult.Plum uniform before L. use Foam beforeL later for Pave.Single.
def Entice {G:Gauge}(P:Teller G)(Q:Target G P)(M:RG.Stage)(L: Side):Prop:=∀ (a W μ:ℝ)(o:Target.Order G W)(C t:ℝ),0 < W→0<μ→0<t→t≤ 1→∀ᶠ x in atTop, Plum G P Q M L x a W μ o C t
lemma petal (G:Gauge)(P:Teller G)(Q:Target G P)(M:RG.Stage)(hp:M.supportExponent+2<Q.exp)(ht:Q.rate≤-(7/16:ℝ)):∃ N:ℕ,∀ L:Side,N≤L.val→Entice P Q M L:=by
    obtain ⟨N,hN⟩:= Mill.projects ht; refine ⟨N,fun L hL a W μ o C t hW hμ ht' hv=>?_⟩; let φ:=pottery G L; let z:=M.supportExponent+2; have he:0≤z:= add_nonneg M.price_pos.le zero_le_two
    have hh : ∀ᶠ x in atTop,∀ (c f : Side)(S:StepData c f) (T:Tube G S),Works P L x S T→Stamp T→∀ (R:Rep G f)(H:Cash W x μ L Q o C T R)(U:Tune H (fire G L x) (thaw G L x))(B:BudgetPoint), B.power=M.power→B.order=M.order→B.threshold=Pressure.temp x→ Mill.Jam H U B Chi.canonical z (pottery G L x) :=by
        by_cases he':∃ D:Patch, D.Branches P.bind G∧ D.L=L∧ D.J=P.j
        swap; · exact Eventually.of_forall fun x c f S T h=> False.elim (he' ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩)
        obtain ⟨D,hD,hX,hY⟩:= he'; filter_upwards [hN L hL D hD M.order M.power Chi.canonical W μ hW hμ o C z he hp] with x hx c f S T h hv R H U B hP hB hf; exact hx c f S T (h.patch hX hY) hv R H U B hP hf hB
    have hz:=Crew.freshVeil Q ht L μ hμ W o C Chi.canonical z he hp
    filter_upwards [hh,hz,mingle (G:=G) L (potP G L Q.halo M) (show 0<μ/4 by positivity) (he:=zero_lt_one) (by norm_num) (pot_bills G L Q.halo M), mingle (G:=G) L (fun x=>2*betaF G x L ^ (-(1/4):ℝ)) (show 0<μ/8 by positivity) zero_lt_two (show -(1/4:ℝ)<0 by norm_num) (Rate.power.mul_left _),crisp G M L a t ht' hv ] with x hh hz ht hu hw
    refine ⟨fun c f S T h hT R H U B hB hA ht he=> ⟨hh c f S T h hT R H U B hB hA he,hz c f S R T H U⟩,fun v he hk=> ht _ _ (Real.exp_pos _).le he hk (by rw [one_mul,← syrup]),fun B hS hB hP he=> ?_⟩
    have ha: Mallow.stems μ L G x= 2*lauge L (μ/8) x 1 G:=by unfold Mallow.stems lauge;ring_nf
    obtain ⟨κ,hκ⟩:= hu (Mallow.stems μ L G x) _ (show 0≤Mallow.stems μ L G x from (by unfold Mallow.stems lauge; positivity)) he (mul_le_mul_of_nonneg_left (hw B hS hB hP) zero_le_two) ha.le
    refine ⟨κ, ?_⟩; rw [show straw μ L G x=2*lauge L (μ/8) x (1/2) G from by unfold straw lauge; ring_nf]; exact hκ
variable {Z:Expenses Q} {D:Rolls s} {Θ:Protection D} {w:Return.Wages} {E:ℕ→ℝ}(R : Register D Z w E)
def Indent (Q:Targets s K)(D:Rolls s):=∀ i j,StepStages j i→Entice (Testing.query s K j i) (Q j i) (s.profile i) (D.L j)
def PaysW (t:ℝ)(U:Delays Θ):=∀ j i,StepStages j i→∀ x,U.betaEntry j≤x→ Plum G _ (Q j i) (s.profile i) (D.L j) x (UVNext.CouplingReset.alphaBound D j) (w j i) (R.μ j i) (R.o j i) (R.c j i) t
lemma donate (V: Delays Θ)(h:Indent Q D)(t:ℝ)(hp:0<t)(ht:t≤1) : ∃ W:Delays Θ,DelayLe V W∧∀ U:Delays Θ,DelayLe W U→PaysW R t U:=by
   have he j:=eventually_transitions j _ _ (fun i (he:StepStages j i)=>h i j he (UVNext.CouplingReset.alphaBound D j) _ _ (R.o j i) (R.c j i) t (R.consumes j i he).1 (R.consumes j i he).2.1 hp ht)
   obtain ⟨x,-,hx,h⟩:=collect_upper V.betaEntry _ he; exact ⟨{V with betaEntry:=x}, ⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ H j i hh x hp=> h j x ((H.beta j).trans hp) i hh⟩
lemma incomesW (Q:Targets s K) (hp:∀ j i, (s.profile i).supportExponent+2<(Q j i).exp) (ht:∀ i j, (Q i j).rate ≤ -(7/16)) : ∃ x:ℕ→ℕ,∀ j i,StepStages j i→∀ L:Side,x j≤L.val→ Entice (Testing.query s K j i) (Q j i) (s.profile i) L:=by
   choose u hx using fun j i=> petal G (Testing.query s K j i) (Q j i) (s.profile i) (hp j i) (ht j i); exact ⟨fromMax u,fun j i h L he=> hx j i L ((le_fromMax u h).trans he)⟩
end YM.PhysicalNext.Repeat.Jams
