import YM.UVExtension.Guild.Loom
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


variable {P Y: (RG.Rep G (A.B.a.S.side (m+1) n))} (H:Guide A.B R.shape N m n P) (W: Zeal R.target R.shape A N m) (k:ℕ)
    (J:Guide A.B R.shape N m n Y) (F:Match.Alliance H J 1 0)(hF:F.units=Equiv.refl _)(h:KinBase P Y)(hv:Opera.Price A.B R.shape N m n Y J)(hb:Y.beta∈band A.B.a (m+1)) (hp:Y.p=(A.B.a.budget (m+1)))
def GleamV : Trio.Offer G (A.B.a.S.side m n):= Trio.ornament (Rain.screens R.target A m) (W.offers k ⟨Y.beta,hb⟩)
def SightV : Trio.Offer G (A.B.a.S.side m n):= Trio.insight (A.B.a.budget m) F (A.B.kin.alpha N m) k (Rain.screens R.target A m) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (W.offers k ⟨Y.beta,hb⟩)
def Tips : Collection.Source G (A.B.a.S.side m n):= Meadow.timbres F (A.B.kin.alpha N m) k (χ:=Chi.canonical)
include hm F hF h hv hb hp
lemma knighthood (u:Site (A.B.a.S.side m n)): Trio.Tidy (A.B.a.budget m) (neighbors (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) u) (SightV R H W k J F hb u)∧ (∀ V,SightV R H W k J F hb u V ≠0 → ¬Healthy (A.B.a.budget m).threshold (neighbors (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) u) V) ∧ ∀ V, ‖SightV R H W k J F hb u V‖≤ Rain.tempe (A:=A) (Z:=R.expense) (m:=m) := by
  let Z:=A.B.a; let V:=A.B.a.S.oneStep m n; let P':=(A.B.a.budget m); let x:=(A.B.a.clock.hatBeta m); let t:= R.pledging; let v:=Z.clock.J (m+1); let j:=Z.clock.J m; let i:=step_paid Z m; let s:=R.inn; let w0: lands A m := ⟨Y.beta,hb⟩; let m':= (Rain.lint R.target A m); let c:=(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))); let hD:= (Guild.hp_width R hm Y).1; let hi:=t.agenda _ _ i|>.1; let hz:=t.conducts.full; let q0:=Chi.canonical; let W':=W.offers k w0; let K:=Trio.heat G (D.L (A.B.a.clock.J (m+1))) (R.expense v j).wanting (Rain.lint R.target A m) (X.p.profile (A.B.a.clock.J m)) x
  have hA:= Boulevard.lays R.shape A V.exact_size F s.chip hm t.jewels hz hi hD hv (Classical.choice (Tree.select _ (Z.clock.op m n).patch.odd_side))|>.1
  have hu l d: P'.Regular Finset.univ (W' l d):= (W.attunes hm hz s t.jewels hD ⟨hi,R.settles _ _⟩ l (fun _=>w0) Set.univ continuousOn_const d|>.smooth 0 (Set.mem_univ _))
  let hW : Trio.tent m' (radiusB x)+4 ≤ c:= by unfold c Trio.base; unfold m' x; omega
  have hY:= Roof.volumic (n:=n) (m:=m) A s.terms|>.2
  let hM:= Match.same_area (H:=H) (J:=J) h.path h.reg h.forced
  let hπ:Y.path=A.B.kin.path N (m+1):= J.laws.intake.received.1
  refine ⟨Trio.prim (A.B.a.budget m) F (A.B.kin.alpha N m) k (Rain.screens R.target A m) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) W' u hA.smooth hu hW (by unfold Trio.base Trio.tent Rain.lint; omega) le_rfl rfl,fun V hx hh=> hx (Trio.scrap P' F (A.B.kin.alpha N m) k (Rain.screens R.target A m) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) W' u le_rfl hW (by unfold Trio.tent Rain.lint; omega) hY rfl hM h.path hF ?_ hh),fun y=>?_⟩
  · exact Trio.caged R.shape A (A.B.a.S.oneStep m n).exact_size (fun i=>Rain.panes R.target A m i) F (fun i=>W.tiers i w0) hb hπ hp s.chip t.conducts.income.grow.1 hm t.jewels hz hi hD hY (fun i=> (Trio.highChair (Rain.lint R.target A m) (radiusB x) i).1) hA h.path hM hF
  have hS: turnFee P'=Height.away (X.p.profile (Z.clock.J m)):= (Rain.jersey (A:=A) (m:=m)).2.2.2
  have ht i (U:Config G (Rain.moor R.target A m i)) (hp: flags P'.threshold U=∅)(o:Site (Rain.moor R.target A m i)): ‖W' i o U‖≤ K:= by
    let B':=Pane.panel A m (Rain.panes R.target A m i); let w:= Boulevard.smiles R.shape A (Rain.panes R.target A m i) (W.tiers i) w0
    have he:= Boulevard.lays R.shape A _ w s.chip hm t.jewels hz hi hD (W.renewed i w0) (Classical.choice (Tree.select B'.ratio B'.patch.odd_side))|>.1
    have hh:= Trio.skin (A.B.a.budget m) U w (A.B.kin.alpha N m) k o he rfl rfl rfl rfl hp; rw [show turnFee (A.B.a.budget m)= _ from hS] at hh; exact hh
  have hh:= Trio.august P' y F (A.B.kin.alpha N m) k (Rain.screens R.target A m) c W' u hA rfl hF hM h.path (fun _=>K) ht hW; rw [hS] at hh; exact hh
lemma faucet :
    let Tap0:= bison (Tips R H k J F) (GleamV R W k hb) (SightV R H W k J F hb)
    Ingredients (lodge (Beam.marquee H (A.B.a.budget m)) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))))) (dummy Tap0) (raiser (A.B.a.budget m)) 0 (Time.forecastK A.B.a m R.scout Y.beta) :=by
  intro Y'
  let P':= (A.B.a.budget m); let x:=(A.B.a.clock.hatBeta m); let i:=step_paid A.B.a m; let R':=Tips R H k J F
  let v:= Rain.tempe (A:=A) (Z:=R.expense) (m:=m); let u:=coverTicket (Rain.lint R.target A m); let E:=(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))
  have he j:= knighthood R hm H W k J F hF h hv hb hp j
  have hm (s t):Nonempty (((Beam.marquee H (A.B.a.budget m)).read R').Moves s t):= Beam.moves _ _ Chi.canonical F s t _
  let c:=Cash.armK (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) x 0 (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).degrees; let f:=Marlin.tithe (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) v P' u
  let w:=Time.forecastK A.B.a m R.scout Y.beta
  have hc:c ≤ w/8:= (Opera.backing A.B R.shape R.pledging.conducts.income hb).trans_eq (by unfold w; ring)
  have hY (y:Site (A.B.a.S.side m n)):(coverNumber P'.B (neighbors (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) y):ℝ)≤u:=by unfold u coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters (Rain.lint R.target A m) (radiusB x) P'.B_pos y _ le_rfl).trans; rw [two_mul]
  have hC:= Rain.jersey (A:=A) (m:=m)
  have hh':P'.supportExponent+1+1 ≤ (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).earn:=by
    have hh := R.pledging.agenda (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) i|>.1; have hp:P'.supportExponent= _:= hC.2.2.1; rw [hp]; linarith only [hh]
  obtain ⟨T,hT,hv'⟩:=Refrain.chargesOut (Marlin.raiser P') H F Chi.canonical hv rfl hh'; let Ψ:=R.inn.terms
  obtain ⟨hx,-,hX,-⟩:= Ψ.allot _ _ i x (A.B.valid.pays m)
  have hw:w= (R.scout (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).pair.strong (betaF G x (D.L (A.B.a.clock.J (m+1)))) Y.beta:= by unfold w forecastK; rw [PriceCompiler.beta_eq A.B.valid m]
  have ht':0 ≤ v:= (norm_nonneg _).trans (he 0|>.2.2 1)
  have hg:f≤ betaF G x (D.L (A.B.a.clock.J (m+1))) ^ (-(1/8:ℝ)):= by unfold f Marlin.tithe; unfold P' v u; rw [hC.2.2.1]; exact hx
  obtain ⟨K,hg⟩:= hX Y.beta (show Next.Scheduling.inBand (betaF G x (D.L (A.B.a.clock.J (m+1)))) Y.beta from (by unfold x; rw [← PriceCompiler.beta_eq A.B.valid m]; exact trial_in hb)) c f (budget_nonneg (hv' 0)) (show 0≤ f from (by unfold f Marlin.tithe; positivity)) (hc.trans_eq (congr_arg (fun x:ℝ=>x/8) hw)) hg
  exact stakes (A.B.a.budget m) (Beam.marquee H (A.B.a.budget m)) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) R' _ _ (Refrain.qualified _ _ _ _ _ _ rfl) hm (hp:= show Payments.Rates _ w c f _ from hw.symm ▸ hg) hT hv' (fun i=>(he i).1) (fun i=>(he i).2.1) (fun i=>(he i).2.2) hY (le_refl f)
variable (T:Crest R ε)(he:Wheeled R H W (ε:=ε) k)

def Chosen := Concert.shapeP H F (Rain.screens R.target A m) k (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (A.B.a.budget m) (W.offers k ⟨Y.beta,hb⟩) (A.B.kin.alpha N m)
-- same Bills, now no history predicate assumptions
include he T
lemma ready : Collection.Local (Guild.Market R H) (A.B.a.budget m) (Chosen R H W k J F hb) (Time.forecastE A.B.a m) (Time.forecastK A.B.a m R.scout Y.beta) :=by
  obtain ⟨k',hx,hK⟩:= fleetFund R hm T H W (Guild.hp_width R hm P).1 he J F h hF hb hv
  let T':= bison (Tips R H k J F) (GleamV R W k hb) (SightV R H W k J F hb); let P':=(A.B.a.budget m); let x:=(A.B.a.clock.hatBeta m)
  have ht:0≤ forecastE A.B.a m:= by unfold forecastE; apply mul_nonneg (credit_pos ..|>.le); exact Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
  have hh: Meadow.Budget (A.B.a.budget m) (lodge (Beam.marquee H (A.B.a.budget m)) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))))).reg T'.regular (Time.forecastE A.B.a m):= by
    refine ⟨_,fun i=> budget_loosen (hx i) ?_,hK⟩; have hp:= T.limited; linarith only [mul_le_mul_of_nonneg_right hp ht,ht]
  have hm (s b) : Nonempty (((Beam.marquee H (A.B.a.budget m)).read (Tips R H k J F)).Moves s b):= Beam.moves _ _ Chi.canonical F s b _
  apply sous (B:=P') (d:=T') (faucet R ‹m<N› H W k J F hF h hv hb hp) hh ; intro s b; exact Marlin.reeds (Beam.marquee H (A.B.a.budget m)) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) _ _ _ s b (hm s b|>.some)
lemma standing (g:G.Simple):
   let a:=A.B.a; let V:=Chosen R H W k J F hb; let X:= Market R H; let t:=A.B.kin.path N m; let z:= branch X t (a.params m).clip (A.B.a.budget m) V (A.B.kin.alpha N m)
   Ingredients (shelves X t (A.B.a.budget m)) z (A.B.a.budget m) (Time.fraction a m) (quoteHard a m R.book Y.beta)∧
     let t':=(finish t (a.params m).clip (A.B.a.budget m) (shelves X t (A.B.a.budget m)) z 0 0).activities
     t'.Valid (A.B.a.budget m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m) ∧ t'.KBound (A.B.a.budget m) (Return.forcing A.B m):=by
  intro a' V X t z; let H':= R.machine; let Q':ℝ→(RG.Rep G (A.B.a.S.side (m+1) n)):=fun _=>Y
  let he':= H'.coverage _ _ (step_paid A.B.a m)
  have hf: Time.credit G (A.B.a.params m) ≤ R.post.cost (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)/4:= (params_eq A.B.valid m) ▸ he'.2
  let W':= Time.now (Q:=Q') A.B hm H'.shops he'.1 hf R.exchange H'.cubic (s':=Set.univ) (fun _ _=>hb); let i:ℝ:=0
  have hr:= ready R hm H W k J F hF h hv hb hp T he
  have hp:= W'.1
  have hK:((A.B.a.budget m)).threshold ≤ 1:=(A.B.a.budget m).threshold_le
  let E:= hr.renew g (A.B.support.cap N m hm.le) (Guild.hp_width R hm P).1 hp.width (A.B.kin.alpha N m) (Return.enough_room ..) (hp.fees i (Set.mem_univ _)) -- align
  refine ⟨E,?_⟩; intro t'; exact hp.closes i (Set.mem_univ _) t' (E.gates ..)
end YM.UVExtension.Guild
