import YM.UVExtension.Wren.Sand
import YM.UVExtension.Camp.Pear
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Upland
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
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
open Reward Wren Steady Span
variable {G:Gauge}{ι:Type} {v:Filter ι} {T:Levels G}
/-!
 Achievement, vacuum side. Read this at a fixed schedule.Levels, no ref resets after
 reporting any b. The amplitudes in the hol conclusion are of complex stage couplings
 and FULL arrays as read in the completion of mask-and-difference norms. Normalized
 arrays: currency costs included, explicitly use that same (linewidth,cutoff)
 and that common arena even as mover bases change with b. No arbitrary convergence test
 series here. Excluded data: v, the field-INdependent unit in Rep.eval, whose exact
 partition at finite cutoff is logically separate from these UV claims.
 -/
open Spire
variable {X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A} {hG:G.Simple} {S: Spire.Uses R hG} {Y:Bolt A}
structure Arc (R:Factor A)(S: Uses R hG)(Y:Bolt A) : Prop where
    atPeak : Y.history=S.realBeat 0
    crowns : Camp.Sign S
    fields : Ends A.B.a A.B.kin.path A.B.kin.alpha
    reports : Free.Report A.B.M X.K
    tax : Roads.Tags.Tax R.shape A.delay

local notation "a!"=> A.B.a
local notation "m!"=> A.B.a.S
local notation "p!"=> S.grove.coins
namespace Arc
variable (S)
def radius (_:Uses R hG):= flatTime A.B.a
def betaK (m n N:ℕ)(b:ℂ): ℂ:= if h:m≤N then (S.fits N n).prays (S.cart N n) S.grove.coins b m h else 0
def view (m n N:ℕ)(b:ℂ): Tabernacle.Readings G (A.B.a.budget m) (A.B.a.S.side m n):= if h:m ≤ N then (S.fits N n).gates (S.cart N n) S.grove.coins b m h else 0
lemma real (m n N)(h:m≤N)(b:ℝ)(hp: (b:ℂ) ∈ ball (0:ℂ) (Upland.Arc.radius S)): let R:= S.realBeat b N n m
     R.path=A.B.kin.path N m ∧ R.clip=((A.B.a.params m)).clip ∧ R.p=A.B.a.budget m ∧
     R.activities.reg=(drawer G _).reg ∧ R.activities.forced=Ovens.Pipes.addr (folio G _) (A.B.a.budget m) ∧ betaK S m n N (b:ℂ)=Complex.ofReal R.beta ∧
     Arc.view S m n N (b:ℂ)=tuning (A.B.a.budget m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m) (R.activities.E,R.activities.K):=by
   intro J; refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
   · rw [betaK,dif_pos h]; exact ((S.fits _ _).really (S.cart ..) (S.token ..) S.grove.coins hp m h).1
   rw [Arc.view,dif_pos h]; exact (S.fits _ _).realX (S.cart ..) (S.token ..) S.grove.coins hp m h
lemma finiteCut (m n N)(h:m≤N) : AnalyticOnNhd ℂ (betaK S m n N) (ball (0:ℂ) (radius S)) ∧ (∀ i∈ ball (0:ℂ) (radius S), ‖betaK S m n N i‖≤3*A.B.a.clock.hatBeta m) ∧ AnalyticOnNhd ℂ (view S m n N) (ball (0:ℂ) (radius S))∧∀ i∈ball (0:ℂ) (radius S), ‖view S m n N i‖ ≤ Camp.soft:=by
   obtain ⟨H,K⟩:= (S.fits _ _).nowBeta (S.cart N n) S.grove.coins m h; obtain ⟨F,hF⟩:= (S.fits _ _).lamps (S.cart N n) S.grove.coins m h
   have hS:IsOpen (Camp.Broad A.B.a):= isOpen_ball
   unfold view betaK; simp_rw [dif_pos h]; exact ⟨H.analyticOnNhd hS,K,F.analyticOnNhd hS,hF⟩
variable {S}(a:Arc R S Y)
include a
-- Disk independent of cutoff and period. Full not subsequence.
lemma uv (m n:ℕ): Camp.SummitUV (radius S) (betaK S m n) ∧ Camp.SummitUV (radius S) (Arc.view S m n):=by
   have he (b:ℝ)(h:|b|< radius S):= Camp.artistry S n a.crowns a.fields b (show (b:ℂ)∈ Broad a! from mem_ball_zero_iff.mpr ((Complex.norm_real b).trans_lt h)) m
   refine ⟨Camp.viva _ (flat_pos _) (3*A.B.a.clock.hatBeta m) ?_ ?_, Camp.viva _ (flat_pos _) Camp.soft ?_ ?_⟩
   · intro i; by_cases h:m≤ i; exact ⟨(finiteCut S m n i h|>.1.differentiableOn),(finiteCut S m n i h).2.1⟩
     unfold betaK; simp only [dif_neg h,norm_zero]; exact ⟨differentiableOn_const _,fun _ _=> mul_nonneg (by norm_num) (zero_le_one.trans (A.B.a.fits.delayed _|>.le))⟩
   · intro b h; apply ((he b h).2.post Complex.continuous_ofReal).copy; filter_upwards [eventually_ge_atTop m] with i hi; exact (real S m n i hi b (mem_ball_zero_iff.mpr ((Complex.norm_real b).trans_lt h)) |>.2.2.2.2.2.1).symm
   · intro i; by_cases h:m≤ i; exact ⟨(finiteCut S m n i h).2.2.1.differentiableOn,(finiteCut S m n i h).2.2.2⟩
     unfold view; simp only [dif_neg h,norm_zero]; exact ⟨differentiableOn_const _,fun _ _=> by norm_num [Camp.soft,Oriel.rim]⟩
   intro b h; apply (he b h).1.copy; filter_upwards [eventually_ge_atTop m] with i hi; exact (real S m n i hi b (mem_ball_zero_iff.mpr ((Complex.norm_real b).trans_lt h))|>.2.2.2.2.2.2).symm
lemma exists_trial (N n:ℕ)(b:ℝ)(h: |b|< radius S) :
    (∃! β:ℝ,S.Trial N n b β) ∧ RG.Shoot.Competes A.B.bake n N 0 (S.realBeat b N n) ∧ (S.realBeat b N n 0).beta=A.B.a.clock.bar+b ∧
      (∀ β:ℝ,S.Trial N n b β → betaK S N n N (b:ℂ)= Complex.ofReal β) :=by
   have hp: (b:ℂ)∈Camp.Broad a!:=mem_ball_zero_iff.mpr ((Complex.norm_real b).trans_lt h)
   exact ⟨⟨_, S.terminates N n hp, fun β=> S.only N n hp⟩,S.ticking N n hp, S.hits N n hp, fun β ht=> (S.only N n hp ht).symm ▸ ((real S N n N le_rfl b hp).2.2.2.2.2.1)⟩
 
lemma centered : History.Selected (A.B.bake.make (S.realBeat 0)):=by rw [← a.atPeak]; exact Y.choice -- inspect
end Arc
end YM.UVExtension.Upland
#print axioms YM.UVExtension.Upland.Arc.uv
