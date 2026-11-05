import YM.UVExtension.Dales.Broil
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Dales
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
open Guild Tabernacle
open Whirl PhysicalNext.Repeat.Graces
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ}{ε : ℝ}
local notation "R₁" => A.B.a.budget (m+1)
local notation "B" => A.B.a
local notation "Y" => A.B.a.clock.hatBeta (m+1)
local notation "Pv" => mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0
variable (hG:G.Simple) (t:Crest R ε) (H: Tour R N m n ε) (d:Cham A.B.a (m+1) n)
variable (v:Fin 4→ Valve (m+1) n A.B.a d)
    (hv:∀ i,‖place A.B.a (m+1) n d (v i)‖ ≤1){u:ℝ}(T:Paperwork R.shape ε u A.delay) {C:ℝ}(hc:InsideB (A.B.a.clock.hatBeta (m+1)) C)
local notation "B₀"=> A.B.a.clock.hatBeta m
local notation "N₀"=> A.B.a.clock.J m
local notation "N₁"=> A.B.a.clock.J (m+1)
local notation "T₁"=> betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))
local notation "d₁"=> D.L (A.B.a.clock.J (m+1))
variable {V:Cham A.B.a m n}(he : Tour.Hind R hG t H d V)
open Tour
local notation "Y₀" => H.atTopH
local notation "η!" => vi d v
local notation "W#" => billA R T hc
variable (JJ:(u:Canvas (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))) realcap (Fin 4))→Guide A.B R.shape N m n (openingA R (N:=N) d v u))
lemma tintA (s:Arbor): openingA R (N:=N) d v (billA R T hc s)= mount R N (m+1) n (songs d v (mapsA s)).val (art Y C (s.val none)) 0:=by
    unfold openingA freshen; rw [modE R d v]; rw [PriceCompiler.beta_eq A.B.valid m]; rfl -- `hc` dep
include hv H
include JJ in
set_option maxHeartbeats 600000 in
lemma latched (s:Arbor): cu R H d (spent R d v hv T hc s)= Guild.Collect R H.atTopH H.W (k:=H.k) η! JJ (billA R T hc s):= by
    have ht:= tintA R (N:=N) d v T hc s; let K:= H.oracle R d (spent R d v hv T hc s) 0
    have hk: (Payroll.stageNote (billA R T hc s): lands A m)= ⟨art Y C (s.val none),(spent R d v hv T hc s).1⟩:=Subtype.ext (congr_arg RG.Rep.beta ht)
    unfold Guild.Collect; rw [hk]; exact sameArts _ _ _ (show KinBase Pv Pv from ⟨rfl,rfl,rfl,rfl,rfl⟩) (K.links R H.atTopH) _ rfl rfl _ _ (show Cousin _ _ from (by rw [← ht]; exact ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩))
include T hG he hc t
lemma high : Concert.Charm lever (Yard.rake Y) (fun s:Arbor=>Tour.bonus R H d (spent R d v hv T hc s))∧ ∃ f:Mark→ Dales.Hold A.B.a m n V, Bumps lever.span f∧(∀ z∈lever.span, ‖f z‖ ≤ u)∧ ∀ s,f (lever.call s)= place A.B.a m n V (H.royals R hG t d (spent R d v hv T hc s) he):= by
    choose J hJ using fun x=> topbar R H d v hv x; have hz:= H.hm; have hp := notch R T (m:=m)
    obtain ⟨hh,hA,hV,hF⟩:= Guild.shaft R hz H.atTopH H.W t H.hr (vi d v) T.gain hp (staple hc) (Dales.fetes R H d v hv) J hJ hG u (T.chord _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)|>.2.2) T.charter.hit -- _ hb
    let v0:= resultant R H.atTopH H.W (k:=H.k) η! hp (staple hc) J; let g:= Guild.driftE R H.atTopH H.W (k:=H.k) η! hp (staple hc) J; let w s:= cu R H d (spent R d v hv T hc s); let q s :=H.royals R hG t d (spent R d v hv T hc s) he
    constructor
    · rw [show (fun s=>Tour.bonus R H d (spent R d v hv T hc s))=g from ?_]; apply (congr_arg (fun x=>Concert.Charm lever (Yard.rake x) g) (PriceCompiler.beta_eq A.B.valid m)).mpr hh -- hmm dep
      funext s
      exact congr_arg (fun x=> Averaging.delta ((Guild.Market R H.atTopH).read x)) (latched R H d v hv T hc J s)
    have hs(x:Arbor): ((v0 x).activities.E,(v0 x).activities.K)=(q x).val:= by
      exact congr_arg (fun i: Collection.Source G (A.B.a.S.side m n)=> let U:= Guild.Market R H.atTopH; let j:= A.B.kin.path N m; let p:= A.B.a.budget m; let c:= (A.B.a.params m).clip; let F:= finish j c p (shelves U j p) (Collection.branch U j c p i (A.B.kin.alpha N m)) 0 0; (F.activities.E,F.activities.K)) (latched R H d v hv T hc J x).symm
    have hu:= fundedP m B; refine heading (A.B.a.budget m) V _ _ u q hu.1 hu.2 (t.positive.le.trans T.charter.hit) ?_ ?_
    · have hQ : sheetE (A.B.a.budget m) ∘ (fun i=>(q i).val)= (fun i=> sheetE (A.B.a.budget m) ((v0 i).activities.E,(v0 i).activities.K)) := by
        funext i t k; exact congr_arg (fun x=>sheetE (A.B.a.budget m) x t k) (hs i).symm
      rw [hQ]; exact hV
    · rw [show sheetK (A.B.a.budget m) ∘ (fun i=>(q i).val)=(fun i=>(v0 i).activities.K) from ?_]; exact hF
      funext i; change (q i).val.2= _; exact (congr_arg Prod.snd (hs i)).symm
end YM.UVExtension.Dales

#print axioms YM.UVExtension.Dales.latched
#print axioms YM.UVExtension.Dales.high
