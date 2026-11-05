import YM.UVExtension.Guild.Pay
import YM.UVExtension.Concert.Pure
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Guild
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ} (hm:m<N) {ε:ℝ}


-- payroll scalar tier extra sharp; output invests chosen C coeff BEFORE L
structure Crest (ε:ℝ) : Prop where
  pipes : Roof.Pew R.v R.t R.prices R.recordP R.span R.shape (Roof.wind R.menu) A.delay ε
  peak : Height.Rich R.shape ε A.delay
  positive : 0<ε
  limited : ε≤1/16
  falls (m:ℕ):turnFee (A.B.a.budget m)* Boulevard.gold G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) + Boulevard.gold G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) + turnFee (A.B.a.budget m)*((gleam (A:=A) (C:=R.target) (m:=m))*Real.exp (preExponent (A.B.a.budget m) * coverTicket (Rain.lint R.target A m))) ≤ ε*forecastE A.B.a m

variable (T:Crest R ε)
   {P:(RG.Rep G (A.B.a.S.side (m+1) n))}(H: Guide A.B R.shape N m n P) (W:Zeal R.target R.shape A N m)
   (hD:WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m)) (hP:P.p=(A.B.a.budget (m+1)))

def shoal (ε:ℝ) (A: Alloy X D) (m:ℕ):= (ε+2*ε)*forecastE A.B.a m + turnFee (A.B.a.budget m)*(Boulevard.gold G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)) + (Boulevard.gold G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))
structure Wheeled (d:ℕ):Prop where
  helm (Q:(RG.Rep G (A.B.a.S.side (m+1) n)))(H':Guide A.B R.shape N m n Q) (M: Match.Alliance H H' 1 0):KinBase P Q→ M.units=Equiv.refl _ → Q.beta∈ band A.B.a (m+1) → Opera.Price A.B R.shape N m n Q H' → Meadow.Budget (A.B.a.budget m) (Beam.marquee H (A.B.a.budget m)).reg (Meadow.timbres (χ:=(Chi.canonical)) M (A.B.kin.alpha N m) d).logRead (shoal ε A m)
  year : ∀ y:lands A m,∀ i:Site (A.B.a.S.side m n),(A.B.a.budget m).supBounds i (neighbors (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) i) (Trio.ornament (Rain.screens R.target A m) (W.offers d y) i) (gleam (A:=A) (C:=R.target) (m:=m))
include T hD hP hm
lemma wheels : ∀ᶠ d:ℕ in atTop,Wheeled R H W (ε:=ε) d:= by
  have hg:0< Boulevard.gold G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m):= by rw [gold, ← PriceCompiler.beta_eq A.B.valid]; exact Real.rpow_pos_of_pos (zero_lt_one.trans (A.B.a.fits.delayed _)) _
  filter_upwards [retire R hm H hP hD (Boulevard.gold G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)) hg, Rain.uv_shoePay R.pledging hm R.inn (R.settles _ _) R.floor W hD] with d hd hx
  refine ⟨fun Q H' M h hh hv he=> ?_,hx⟩
  have he':= Roof.uvChairs R.pledging.conducts T.peak R.pledging.jewels T.pipes R.pledging.agenda hm (h.point.symm.trans hP) hv H H' he M hh h.path h.reg h.forced
  let v':=A.B.a.S.oneStep m n; have hq:= Boulevard.suns R.shape A R.inn.chip hm v'.exact_size H'; let X':=ships A.B N m n
  let hu : X'.down.Bounds X'.low (A.B.a.params m).width (A.B.a.params m).paths (A.B.a.clock.loopCap m):= A.B.support.cap _ _ hm.le
  exact Meadow.candles M (A.B.a.budget m) (A.B.kin.alpha N m) d (Meadow.podiumAll M (A.B.a.budget m) (A.B.kin.alpha N m) h.path.symm h.reg h.forced hh he' rfl hu hD hq.1 hq.2.2) (hd Q H' M h hv hh)

omit hP
lemma fleetFund {k:ℕ} (he: Wheeled R H W (ε:=ε) k) {Q:(RG.Rep G (A.B.a.S.side (m+1) n))}(H':Guide A.B R.shape N m n Q) (M: Match.Alliance H H' 1 0)(hp:KinBase P Q)(hx:M.units=Equiv.refl _)(hv:Q.beta∈ band A.B.a (m+1))(hg : Opera.Price A.B R.shape N m n Q H'):
    let G':= Concert.shapeP H M (Rain.screens R.target A m) k (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (A.B.a.budget m) (W.offers k ⟨Q.beta,hv⟩) (A.B.kin.alpha N m)
    let C:= Concert.bookA (Beam.marquee H (A.B.a.budget m)) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (A.B.a.budget m)
    Meadow.Budget (A.B.a.budget m) C.reg G'.logRead ((ε+2*ε)*forecastE A.B.a m+ ε*forecastE A.B.a m) :=by
  intro G' C
  let u:=Trio.ornament (c:=(A.B.a.S.side m n)) (Rain.screens R.target A m) (W.offers k ⟨Q.beta,hv⟩)
  let d:= (Rain.gleam (A:=A) (C:=R.target) (m:=m))
  let s:= d*Real.exp (preExponent (A.B.a.budget m) *coverTicket (Rain.lint R.target A m))
  have hU := he.year ⟨Q.beta,hv⟩
  have hW : 0≤ d := (hU 0).1
  have hF : Meadow.Budget (A.B.a.budget m) (Marlin.leap (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) u s := by
    refine ⟨fun _=>d,fun i=>?_,fun i=>⟨?_,hU i⟩⟩; swap
    · rw [show u i= _ from Trio.orchard ..]; apply Meadow.regularA; intro j _; apply CouplingShape.reg_scale
      have hi v: (A.B.a.budget m).Regular Finset.univ (W.offers k ⟨Q.beta,hv⟩ j v):=(W.attunes hm R.pledging.conducts.full R.inn R.pledging.jewels hD ⟨(R.pledging.agenda _ _ (step_paid A.B.a m)).1,R.settles _ _⟩ j (fun _=> ⟨Q.beta,hv⟩) Set.univ continuousOn_const v |>.smooth 0 (Set.mem_univ _))
      let W':= W.offers k ⟨Q.beta,hv⟩ j
      have hg : (A.B.a.budget m).Regular Finset.univ (Trio.froth W') := by rw [show Trio.froth W'=∑ v,W' v from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun i _=> hi i
      exact Slide.regular _ _ (CouplingShape.reg_sub hg (CouplingShape.reg_const _)) (fun v=> (neighbors_mem ..).2 ((Slide.village ((Rain.screens R.target A m) j).ge i v).trans (by unfold Trio.base; have hz:=j.isLt; omega)))
    apply budget_finite
    · intro i; split; exact mul_nonneg hW (Real.exp_pos _).le; rfl
    rw [Finset.sum_eq_single i]; rw [if_pos (show ((Marlin.leap (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) i).site=i from rfl)]
    · apply mul_le_mul_of_nonneg_left _ hW; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (headline (A.B.a.budget m) |>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)) (A.B.a.budget m).B_pos i (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (by omega)).trans; rw [two_mul]
    · intro j hj he; exact if_neg he
    simp
  let v:= Trio.insight (A.B.a.budget m) M (A.B.kin.alpha N m) k (Rain.screens R.target A m) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (W.offers k ⟨Q.beta,hv⟩)
  obtain ⟨f,hf,h⟩:= Marlin.reg_bison (Beam.marquee H (A.B.a.budget m)) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) (Meadow.timbres M (A.B.kin.alpha N m) k) u v (he.helm Q H' M hp hx hv hg) hF
  refine ⟨f,fun i=>budget_loosen (hf i) ?_,h⟩
  have hk:=T.falls m; unfold shoal s d; linarith only [hk]
end YM.UVExtension.Guild
