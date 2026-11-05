import YM.UVExtension.Yard.Allowance
import YM.UVExtension.Lamppost.Grace
import YM.UVExtension.Guild.Round
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


open Payroll
variable {P:(RG.Rep G ((A.B.a.S.side (m+1) n)))}(H: Guide A.B R.shape N m n P) (W:Zeal R.target R.shape A N m)
   (hD:WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m)) (hP:P.p=(A.B.a.budget (m+1)))
   {k:ℕ} (T:Crest R ε)(he:Wheeled R H W (ε:=ε) k) (v:Fin 4→ Juice G (A.B.a.S.side (m+1) n))
   (U: Vision R ε) (hz: Chateau G (D.L (A.B.a.clock.J (m+1))) ε (X.p.profile (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m)) {b:ℝ} (hp:InsideB (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))) b)
   (h:Festa (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) H v realcap (hearts G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)))
variable (J:(u:Canvas (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))) realcap (Fin 4))→Guide A.B R.shape N m n (freshen u P v))
    (hJ:∀ d, Opera.Price A.B R.shape N m n (freshen d P v) (J d))

variable (hG:G.Simple) (t:ℝ)
    (hg: Yard.Grants G (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) t (Pane.cloak D (A.B.a.clock.J (m+1))) ε) (ht:ε ≤ t)

def driftE (u:Arbor):ℝ:= let v0:=Collect R H W v J (k:=k) (maple hz hp u)
    Averaging.delta ((Guild.Market R H).read v0)
include hm R in
lemma hp_width (P: (RG.Rep G ((A.B.a.S.side (m+1) n)))): WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m) ∧ Geo.Width (A.B.a.budget m) (A.B.a.params m).clip (A.B.a.params m).width:= by
  have hT:= R.machine.passes (Q:=fun _=>P) (l:=∅) hm (by simp)|>.1
  exact ⟨hT.decent,hT.width⟩

abbrev resultant (u:Arbor):= let V:=Collect R H W v J (k:=k) (maple hz hp u); let X:=Market R H; let Y:=shelves X (A.B.kin.path N m) (A.B.a.budget m); finish (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) Y (branch X (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) V (A.B.kin.alpha N m)) 0 0
include hG T h hz ht he U hJ hg hm
lemma shaft : Charm lever (Yard.rake (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1))))) (driftE R H W (k:=k) v hz hp J)∧
    let f:= (resultant R H W (k:=k) v hz hp J)
    (∀ i,smoothP (A.B.a.budget m) (drawer G (A.B.a.S.side m n)).reg (f i).activities.E) ∧ Nonempty (ticketR lever (A.B.a.budget m) (drawer G (A.B.a.S.side m n)).reg (A.B.a.budget m).supportExponent (fun i=>(f i).activities.E) (fun _=>t * δE (A.B.a.clock.hatBeta m)))∧
     Nonempty (Atlas (bell (Ovens.Pipes.addr (folio G (A.B.a.S.side m n)) (A.B.a.budget m)) (A.B.a.budget m).B (A.B.a.budget m).supportExponent) lever (fun d i V=> (f d).activities.K i V) (fun _=>t*A.B.a.clock.forcedAllowance m)) := by
  let p:=(A.B.a.budget m); have ht':= hp_width R hm P
  obtain ⟨hS,⟨L⟩,⟨Q⟩⟩:= Guild.earns R hm H W ht'.1 T he v U hz hp h J hJ
  let v0:=fun d:Arbor=>Collect R H W v J (k:=k) (maple hz hp d)
  have hZ:= params_eq A.B.valid m; let Y:=Yard.quoteT ε G (X.p.profile (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m)
  have hw :p.threshold ≤2*Pressure.fiery G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1))):=by rw [← H.laws.data.funds.length_eq]; exact H.laws.data.room.temperatures
  have hb:=Rain.jersey (A:=A) (m:=m)
  obtain ⟨hx,hY,hh⟩:= hg.lifts p ⟨hb.2.1,hb.1,hb.2.2.1⟩ rfl rfl hw
  obtain ⟨hc,hA⟩:= hh _ (Boulevard.coupling A N m hm)
  have hpY: Y= Guild.tentPole A m ε := rfl
  constructor
  · obtain ⟨P₁,hp,hK,hq⟩:= (Yard.sale v0 hG L hS (hpY ▸ hx)).claim
    exact ⟨P₁,hp,hK, fun z g=> (hq z g).trans hY⟩
  intro f
  have h' := U _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)
  obtain ⟨η,hη⟩:= h'.returns (Payroll.pay G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)) (by unfold Payroll.pay; rw [← PriceCompiler.beta_eq A.B.valid]; exact Real.rpow_nonneg (zero_lt_one.trans (A.B.a.fits.delayed _)|>.le) _) le_rfl
  change Yard.priceE Y (A.B.kin.alpha N m) (X.p.profile (A.B.a.clock.J m)).width (X.p.profile (A.B.a.clock.J m)).paths (X.p.profile (A.B.a.clock.J m)).clip p G ≤ _ at hA
  change Yard.priceS Y (A.B.kin.alpha N m) (X.p.profile (A.B.a.clock.J m)).width (X.p.profile (A.B.a.clock.J m)).paths (X.p.profile (A.B.a.clock.J m)).clip p G ≤ _ at hc
  -- rewrite aligns with (X.p.profile (A.B.a.clock.J m)) loan
  rw [hpY,← hZ] at hA hc
  -- hpY now changed P? price cast
  let Q₁:=(A.B.kin.path N m); let V:= (A.B.a.params m)
  obtain ⟨hs,hQ,⟨hq⟩⟩:= Yard.result v0 Q₁ V.clip hG L hS ht'.1 (A.B.support.cap _ _ hm.le) ht'.2 Q (hpY ▸ hx) hA hc hη
  refine ⟨hs,hQ,Lamppost.raiseCredit _ _ hq (fun z _=> ?_)⟩
  have hf:= T.positive
  exact mul_le_mul ht h'.travel (Real.exp_pos _).le (hf.le.trans ht)
end YM.UVExtension.Guild
