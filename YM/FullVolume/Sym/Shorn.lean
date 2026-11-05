import YM.FullVolume.Sym.Able

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
open Ovens Roof Rain Chord Mallow Progress.DirectedRecipe Time Next.Scheduling.Clock Next.Scheduling.Instrument
open UVNext.CouplingReset -- sharp Delta:
variable {G:Gauge} {s:Sheet G} {D:Rolls s} {Θ: Protection D} {F : ℕ→ℕ→Postage}(A:Time.Scouts (F:=F))
variable {v t q : ℝ}
-- Sphere in Grain with u fixed. Release closure.
section years
variable {M:MapPrices}(R:Targets s M) {V: Delays Θ} {d:ℝ}
def offered (i j:ℕ) (x:ℝ) (q v d t:ℝ) := let P:=s.profile i; let u:=chores G P v x; let y:= x+G.slopeConstant*Real.log (D.L j).val -- D skipped
   let α:= UVNext.CouplingReset.alphaBound D j; let r:=(R j i).halo
   q≤ fire G (D.L j) x /4 ∧
   (∀ (c:Side)(B:BudgetPoint)(X:ℕ→RegularAddress c)(Y:sun→ ℕ→ Config G c→ℝ), sanction B X Y (fire G (D.L j) x/2) (good_gross G (D.L j) x) → (∀ t', Meadow.Budget B X (Y t') (spiceF G (D.L j) r P t x)) → sanction B X Y q u) ∧
   ∀ B:BudgetPoint,Time.Same P B→B.B=cover x→B.threshold=plain.t x→ regularNeed G B P.clip P.width P.paths α u ≤ d*δE x ∧∀ β,Next.Scheduling.inBand y β→ ∃ a κ, Real.exp (-Payments.Pairing.kGoal (F j i) y β) ≤ d*plain.w x ∧ 2*softNeed G B P.clip P.width P.paths α u ≤ a ∧ Payments.Rates B.B (Real.exp (-Payments.Pairing.kGoal (F j i) y β)) ((A j i).pair.strong y β) a κ
-- for E0 choose calls leave pre-calibration q gains.

structure Savvy (V: Delays Θ) (q v d t : ℝ) : Prop where
   sphere : sphere q v t
   eta : 0<d
   emits : ∀ j i,StepStages j i→∀ x,V.betaEntry j≤x→ offered (D:=D) A R i j x q v d t

lemma scraps (g:G.Simple)(W : Delays Θ)(hc: sphere q v t)(hd: v ≤ d):∃ U:Delays Θ, DelayLe W U∧∀ Y:Delays Θ, DelayLe U Y→Savvy  A R Y q v d t:=by
  have hh:= hc; obtain ⟨hp,hq,hv,h,u,hu,hz,H⟩:= hh; let f j:= G.slopeConstant*Real.log (D.L j).val; have hy := hv.trans_le hd
  have hx j i :∀ᶠ x in atTop,offered (D:=D) A R i j x q v d t:= by
    let P:= s.profile i; let b:= (R j i).halo; let L:= D.L j; let α:= alphaBound D j
    filter_upwards [cool_fire G L q, cold G L b P q v t hv hz,reunite G P (A j i) hv h (f j) α (mul_nonneg (Gauge.slopeConstant_pos g).le (Real.log_nonneg (by exact_mod_cast (D.L j).pos))),profits (F j i) (f j) d hy, show_width G P hy hv h hd α] with x hv hp he hb ho
    refine ⟨hv,fun c B X Y hs h' => sanctioned_mono (H G _ _ X Y _ _ _ ?_ hs h') hp,fun B hB hf hm=> ⟨ho _ hB hm,fun β hβ=>?_⟩⟩
    · linarith
    obtain ⟨a,b,hA,hx⟩:= he B hB hf hm β hβ; exact ⟨_,_,hb _ hβ,hA,hx⟩
  obtain ⟨x,-,hb,hx⟩:= collect_upper W.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i (_:StepStages j i)=>hx j i))
  exact ⟨{W with betaEntry:=x}, ⟨hb,le_rfl,le_rfl,le_rfl⟩, fun _ h'=> ⟨hc,hy,fun j i hi x hh=>hx j x ((h'.beta _).trans hh) i hi⟩⟩
end years
section earn
variable {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R: Roost.Factor A}
    {N m n:ℕ} {d : ℝ} (g:G.Simple) (H : Chord R N m n t t) (h:Degree R.shape R.scout A.delay) (hq: Savvy R.scout R.target A.delay q v d t)
local notation "I"=> A.B.a.clock.J (m+1)
local notation "J"=> A.B.a.clock.J m
local notation "S"=> A.B.a.S.side m n
local notation "W"=> A.B.a.budget m
local notation "L"=> D.L I
local notation "Γ"=> A.B.a.clock.hatBeta m
local notation "φ"=>fire G L Γ
local notation "p₀"=> (X.p.profile J)
variable {Y:Mist A.B.a m (fire G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)) (thaw G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))}
variable {F:sun→ Chord.Flight A N m n}(hV:SectorOn (A:=A) F Y)
def PreLoop (H:Chord R N m n t t) (x: Flight A N m n):= H.source x
local notation "h'"=> H.listing (F tip)
local notation "X₀"=> Chord.source H ∘ F
local notation "u"=> chores G p₀ v Γ
local notation "α"=>alphaBound D I
local notation "γ"=> A.B.kin.alpha N m
local notation "B"=> (A.B.a.budget m)
local notation "z"=> A.B.a.S.side m n
set_option quotPrecheck false
local notation "k"=> (R.target I J).halo
local notation "δ'"=> Averaging.delta
include H
lemma shining : Chord.bright R m t t=spiceF G L (R.target I J).halo p₀ t Γ:=by
  obtain ⟨hz,hp,h,s⟩:= Rain.jersey (A:=A) (m:=m); unfold Chord.bright spiceF chores Trio.stout preExponent; rw [show forecastE A.B.a m= _ from (by rw [Time.forecastE,params_eq A.B.valid m]; rfl : forecastE A.B.a m=Time.credit G (X.p.profile (A.B.a.clock.J m))*δE Γ),h,s]; rfl
-- installed exact after last widen
local notation "X'"=> A.B.kin.path N m
local notation "b"=> (A.B.a.params m).clip
local notation "N'"=> Collection.shelves (h') (X') (B)
local notation "E'"=> X₀
local notation "V"=> fun i:sun=> petalsC (h') (X') b E' (B) γ i
include hV
lemma reflected_at (i:sun) : (H.moment (F i)).activities = (finish X' b B N' (V i) 0 0).activities ∧ (H.moment (F i)).beta=(F i).val.beta+γ+δ' ((h').read ((E') i)):= by
  have hp: (h') = H.listing (F i):= mist_layout H hV Jams.tip i
  dsimp only []; rw [hp]; exact ⟨rfl,rfl⟩
local notation "Vo"=> fun x:sun=> Chord.moment H (F x)
 
include g h hq hV
local notation "e"=> A.B.a.clock.allowance m
local notation "κ"=> A.B.a.clock.forcedAllowance m
set_option quotPrecheck false
set_option maxHeartbeats 500000 in
lemma qualifiedL : let T:= h'
    sanction B T.reg (fun i:sun=> ((E') i).logRead) q u ∧
    Rebar q (phraseS (fun i:sun=> ((Vo i).beta - (F i).val.beta - γ))) (u/(B).threshold^2) ∧
    Acquittal (drawer G z).reg B (fun i:sun=> (Vo i).activities.E) q (d*e) ∧
    league (fun i:ℕ=> (Pipes.addr (folio G z) B i).support) (B).B (fun i:sun=> (Vo i).activities.K) (B).supportExponent (q/2) (d*κ):=by
   obtain ⟨hE,hK⟩:= cool H h hV; have hQ:= hq.emits I J (step_paid A.B.a m) Γ (A.B.valid.pays m)
   have hq' := hq.sphere.2.1; have hv:(0:ℝ)<v := hq.sphere.2.2.1; have hs:1≤q:=by linarith
   obtain ⟨hy,hQ,H'⟩:= hQ
   intro T; let P':= b; let Y':=A.B.a.params m; have hx:= params_eq A.B.valid m
   have hy' i:Meadow.Budget B T.reg (((E') i).logRead) (spiceF G L k p₀ t Γ):=by
     have hp:= H.fill_price (F i); rw [show T=H.listing (F i) from mist_layout H hV tip i,← shining H]
     exact ⟨hp.cheap.choose,hp.cheap.choose_spec.2,fun j=>⟨hp.smooth j,hp.cheap.choose_spec.1 j⟩⟩
   let F'(i:sun):= ((H.moment (F i)).beta - (F i).val.beta-γ)
   have hA : sanction B T.reg (fun i:sun=>((E') i).logRead) q (u):= hQ _ _ T.reg _ hE hy'
   refine ⟨hA,⟨hs,div_nonneg (show 0≤u from ?_) (sq_nonneg _),?_⟩,?_⟩
   · unfold chores; have hh : 0 ≤ e:= Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _; exact mul_nonneg hv.le (mul_nonneg (Time.credit_pos ..).le hh)
   · have he : F'=fun i:sun=> δ' (T.read (E' i)):=by ext i; unfold F'; rw [(reflected_at H hV i).2]; unfold T; ring
     change ∀ w η,Stripe w q η → ‖FullVolume.Ray.trace w (phraseS F')‖ ≤_
     intro w η hz; rw [he,mix_made]; exact tipped g hy' hA w η hz
   have he':= A.B.support.cap N m H.paid.le; have hd:= decentA H h
   let w0:= F Jams.tip; let β₀:=w0.val.beta
   have hb : β₀ ∈ band A.B.a (m+1):= w0.property.2
   have hY := (Roof.coating H.earns.conducts H.paid (R:=fun _=>w0.val) (s:=Set.Icc (0:ℝ) 1) (fun _ _=> hb)).width
   have hP:= H' B (show Time.Same _ _ from hx ▸ (show Time.Same _ _ from ⟨rfl,rfl,rfl⟩)) rfl ((Deployment.clock_eqns _ _).2.2.2.2.2.2)
   have hs' : |γ| ≤ α:= within_alpha H.paid
   let U:= V
   have ht: Acquittal (N').reg (B) (fun i:sun=> (U i).regular) q (d*e):= by
     apply inkable _ _ (passport (X:=E') g hy' hA hs he' hY hd α hs') ?_
     let x:= u; suffices hm: regularNeed G B b (A.B.a.params m).width (A.B.a.params m).paths α x ≤ d* e from hm; rw [show b=(p₀).clip from congr_arg Stage.clip hx, show (A.B.a.params m).paths=_ from congr_arg Stage.paths hx, show (A.B.a.params m).width=_ from congr_arg Stage.width hx]; exact hP.1
   simp_rw [(reflected_at H hV _).1] -- replace only LHS under binder
   refine ⟨padded _ (B) ht,?_⟩
   let C:= A.B.a.clock.hatBeta (m+1); have hβ : inBand (betaF G Γ L) β₀:= by rw [← beta_eq A.B.valid]; exact trial_in hb
   obtain ⟨A',r,hK',hV',hr⟩:= hP.2 β₀ hβ
   let x :ℝ := ((R.scout I J).pair.strong (betaF G Γ L) β₀); let y :ℝ:= Real.exp (-Payments.Pairing.kGoal (R.book I J) (betaF G Γ L) β₀)
   have hf:1≤q/2:=by linarith
   have hu : league (fun i=> ((N').kernel i).support) (B).B (fun i=>(U i).forced) ((B).supportExponent+1) (q/2) x:=by
     obtain ⟨f,h,hx'⟩:= hK β₀ hb; rw [forecastK, PriceCompiler.beta_eq A.B.valid] at h; exact ⟨f,h,fun i U=>(hx' i U).lessen hf (by linarith)⟩
   have hU:= leg_on g hy' hA hs he' hY hd α («γ»:=γ) hs' hq'; obtain ⟨f,hF,hφ⟩:= hU -- path inference clip implicit
   have hΛ : 2*softNeed G B b (A.B.a.params m).width (A.B.a.params m).paths α u ≤ A':= by rw [show b=(p₀).clip from congr_arg Stage.clip hx,show (A.B.a.params m).paths=_ from congr_arg Stage.paths hx,show (A.B.a.params m).width=_ from congr_arg Stage.width hx]; exact hV'
   obtain ⟨f',hf',hΦ⟩:= employers U B hf hu ⟨f,fun i=> budget_loosen (hF i) hΛ,hφ⟩ (show Payments.Rates (B).B y x A' r from hr)
   refine ⟨f',fun i=> budget_loosen (hf' i) ?_,hΦ⟩; rw [(Deployment.clock_eqns _ _).2.2.2.2.1]; exact hK'
end earn
end YM.PhysicalNext.Repeat.Jams
