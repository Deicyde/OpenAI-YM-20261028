import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Foam
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Rain.Mir
/-!
 # The actual Repeatable Offering on common E/K throughout the interval. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Rain
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
-- compact socket avoids Pie SAM goals; not obligation records encoding analytic estimates.
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} {C:Targets X.p X.K} {Z:Expenses C} {F : ℕ→ℕ→Postage} {S:Time.Scouts (F:=F)} {p : Return.Wages} {s: Set ℝ} {v:ℕ→ℝ} {R:Register D Z p v} {E:ℕ→ℕ→Exchange} {bt:Baton G} {u t : Return.Wages} {Bn:ℕ→ℕ→Booth} {J:ℕ→ℕ→JointLoad.Clockwork.Menu} {P:ℕ→ℕ→JointLoad.Heir.Record} {L : ℕ→ℕ→JointLoad.Folio.Aux} {c c₁ c₂:ℝ} {q:UVNext.CouplingReset.ResetPrices} {η:ℕ→ℝ} {r:ℕ→ℕ→ℕ} {T:Programs X.p} {Y: ℕ→ℕ→Cafe}
    (h : Roof.Sheltered (C:=T) (B:=Y) A bt u t r Bn J P L R S (1/16) (1/16) (1/8) E q η)
    {N m n : ℕ} {Q: UVNext.CouplingReset.In A.B.a m n} {a:ℝ} (hm: m<N)
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "A₀" => A.B.a.S.side m n
local notation "B" => (A.B.a.budget m)
local notation "k" => Rain.lint C A m
local notation "e" => Trio.base k (radiusB x₀)
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "L₀" => D.L Jp
local notation "g" => gold G L₀ x₀
local notation "γ" => A.B.kin.alpha N m
-- Note hL syntax names
variable (H : Roof.Embrasure (U:=A) (Y:=R) (N:=N) (n:=n) Q s a)
variable (hc : Curve (A.B.a.budget (m+1)) Q s) (he : ∀ x∈s,Lives A.B.bake N (m+1) n (Q x) ∧ (Q x).beta ∈ band A.B.a (m+1)) (hh : WorksIn R A.post A.delay S)
   (hx:(C (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).table=X.O) (ht:AsDivisors A.B.a.S) (hl: (Z (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).wanting= -(7/16:ℝ))
    (W:Zeal C R A N m) (d:ℕ)
local notation "D₀" => Meadow.studio (Rain.lint C A m) (radiusB x₀)
set_option quotPrecheck false
local notation "Z₀" => (Z Jp Ip).wanting
local notation "Pu" => (screens C A m)
local notation "Yd" => fun (x:ℝ)=> W.offers d (Rain.noteX H he x)
local notation "O" => Chi.canonical
variable {x:ℝ}
local notation "D₁" => graft H he W d
local notation "f₀" => uptick H d
local notation "b₀" => beacons H he W d
local notation "i₀" => lights H he W d
local notation "p₀" => opening H
local notation "h₀" => ((1/16+2*(1/16:ℝ))*forecastE A.B.a m + turnFee B*g + g)
section locals
include h hm he hh hx H hc
variable (U : Site (A.B.a.S.side m n)) (x : ℝ) (hX:x∈s)
include hX
lemma varnish (hU: Meadow.Budget B H.doors.reg ((f₀ x).logRead) h₀) (hB: ∀ i:Site A₀,(B).supBounds i (neighbors e i) (beacons H he W d x i) (gleam (A:=A) (C:=C) (m:=m))) :
    Collection.Local (opening H) B (paint H he W d x) (forecastE A.B.a m) (forecastK A.B.a m S (Q x).beta):= by
  let D' := lens H; let W':= i₀ x; let V := b₀ x; let Y := f₀ x; let c':= (gleam (A:=A) (C:=C) (m:=m)); let s':= c'*Real.exp (preExponent B*coverTicket k)
  have he' i:= (arete h hm H hc he hh hx W d).2 i|>.smooth x hX
  have hv:0≤ c':=(hB 0).1
  have hF : Meadow.Budget B (leap e) V s':= by
    refine ⟨fun _=>c',fun i=>?_,fun i=>⟨he' i,hB i⟩⟩; apply budget_finite
    · intro i; split; exact mul_nonneg hv (Real.exp_pos _).le; rfl
    rw [Finset.sum_eq_single i]; rw [if_pos (show (leap e i).site=i from rfl)]
    · apply mul_le_mul_of_nonneg_left _ hv; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (headline B|>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters k (radiusB x₀) (B).B_pos i e (by omega)).trans; rw [two_mul]
    · intro j hj he; exact if_neg he
    simp
  have hm : ∀ s b,Nonempty ((H.doors.read Y).Moves s b):= fun s b=> Beam.moves _ _ O _ s b _
  have hp:= Marlin.reg_bison H.doors e (2*e) Y V W' hU hF
  have hs:= Marlin.sous (innings h ‹m<N› H hc he hh hx W d x hX) hp (fun s b=> Marlin.reeds _ _ _ Y V W' s b (hm s b|>.some))
  have hi:= (hh.terms.allot Jp Ip (step_paid A.B.a m) x₀ (A.B.valid.pays m)).2.1
  have hb:= Rain.jersey (A:=A) (m:=m)
  have hP : (h₀) + turnFee (B)*s'≤ forecastE A.B.a m:= by
    have hv:0≤ forecastE A.B.a m:= by unfold forecastE; apply mul_nonneg (credit_pos ..|>.le); exact Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
    have ht:= PriceCompiler.params_eq A.B.valid m
    have hk : preExponent B=stout (X.p.profile Ip):=by unfold preExponent stout; rw [hb.2.2.1]
    rw [show forecastE A.B.a m= credit G (X.p.profile Ip)*δE x₀ from congr_arg (·*δE x₀) (congr_arg (credit G) ht)] at hv ⊢;  unfold s'; rw [hb.2.2.2,hk]; dsimp only at hi; unfold c' gleam Rain.lint; linarith only [hi,hv]
  obtain ⟨f,hf,hG⟩:= hs.cheap
  exact ⟨hs.smooth,hs.family,hs.transforms,⟨f,hf,fun i=>budget_loosen (hG i) hP⟩,hs.expensive⟩
-- Gauge post capture.
omit hX h hc he hm hh hx
variable (M : Return.Wood A.B m n)
def stanzaFee (x : ℝ) := H.payment M x - Meadow.barony (H.houses (H.latch x)) Chi.canonical d γ 0 1
include he hm hX h hc hh hx
lemma sprint (hD: Return.Bookings A.B m n p) (hU: Meadow.Budget B H.doors.reg ((f₀ x).logRead) h₀): Return.atlas A.B N M hD Chi.canonical (radiusW Y) (Q x) (opening H) (paint H he W d x) (stanzaFee H d M x):= by
  have h' := (H.patrons h.conducts he h.agenda h.range hm hX M hD).1
  refine h'.trans (funext fun i=>?_)
  let V:= H.sister (H.latch x)
  have hu:= Marlin.carries B H.doors e (2*e) (uptick H d x) (b₀ x) (i₀ x) i (R:=posting B H.base) (H.fullSong x) (fun _=> ⟨rfl,rfl⟩) (A.B.kin.path N m) (A.B.a.params m).clip (Q x|>.beta) (H.payment M x) γ (Meadow.barony _ Chi.canonical d γ 0 1)
    (innings h hm H hc he hh hx W d x hX) hU (fun i=> Trio.levy B V γ d Pu e (Yd x) i _ _ (twined h hm H he hh x)) (fun s b=> Song.motion B H.base V Chi.canonical γ s b) (fun s b=> Beam.moves H.base B Chi.canonical V s b _)
  exact (Beam.travels H.base B (H.fullSong x) (Q x).beta (H.payment M x) (A.B.kin.alpha N m) i).trans hu -- orientation
end locals
section producer
variable (hm' : ∀ j i,StepStages j i→ (C j i).table=X.O)
include h ht hh hm'
-- Local's Scalar tag receipt for any labeling, not an enumerator.
lemma glazing : Use.Offering A.B S p (radiusW Y):= by
  refine ⟨?_⟩; intro N m p l a b hab s F H hL
  obtain ⟨Z⟩:= Roof.arches h.conducts l hL H (θ:=s) (y:=a) (Set.left_mem_Icc.mpr hab)
  have hc :=hm' _ _ (step_paid A.B.a m)
  let W:= Classical.choice (Rain.learns (R:=R) (A:=A) l h.conducts.income.grow.1 h.conducts.full) -- order
  obtain ⟨d,hD,hE⟩:= (Rain.topped h l Z H hL hh hc ht W isCompact_Icc).exists
  let M:= Classical.choice (Tree.select (A.B.a.clock.op m p).ratio (A.B.a.clock.op m p).patch.odd_side); let t:=Opera.forum (m:=m) (n:=p) A.B R
  exact ⟨opening Z, paint Z hL W d, stanzaFee Z d M,M,t,Chi.canonical,(fun i hi=> sprint h l Z H hL hh hc W d i hi M t (hE i hi)), (fun i hi=>varnish h l Z H hL hh hc W d i hi (hE i hi) (hD i hi)), Rain.blinking h l Z H hL hh hc W d hE hD⟩
end producer
end YM.PhysicalNext.Repeat.Rain
