import YM.FullVolume.Luna.Hours
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna
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
open YM.Source Planned.GuardedAtom Labels MergeProof MergeProof.Matric Extra.Histories Guard Jams
open Next.Scheduling.Clock Instrument
variable {G:Gauge}{P:Teller G} (Q:ConnectedActivityE6.Target G P){p v b t q:ℝ}
open Mallow
open Daisy Lotus Height Blush Graces
open RG.Supply UVNext.CouplingReset Testing Push.PriceCompiler
open Bid
open Next.Foundations
variable {s:Supply.Sheet G}{D:Rolls s}{A: Protection D}{K: MapPrices}{R:Targets s K}{V:Expenses R}{w:ℕ→ℕ→ℝ}{l:ℕ→ℝ}(W:Register D V w l)
local notation "F"=> Labels.frames G
-- actual w amounts arbitrary ≤proof.d.Per-level Bound.Bar. choose fraction before T after P; no Φ overhead after reimbursed.
section amounts
open Extra.Histories.Motion
-- all positivity unconditional incl author budget without Bool. from Vigors.Next
abbrev pearl (M:Stage)(G:Gauge):=Cub.title G M
abbrev crestP (M:Stage)(G:Gauge):=Real.exp M.supportExponent*pearl M G
abbrev lute (M:Stage)(G:Gauge)(d:ℕ):=Push.Local.factor (hol G) (localSection G d) M.supportExponent (pearl M G)
abbrev tipsH (M K:Stage)(G:Gauge)(d:ℕ):= orbitCost ((Labels.frames G).level d)*lute M G d*(crestP K G)
abbrev costP (s:Sheet G)(D:Rolls s)(j i d:ℕ):= Doors.rate (D.L j)/ tipsH (s.profile i) (s.profile j) G d
lemma pearls (M:Stage)(G:Gauge):1≤ pearl M G :=Cub.title_one ..
lemma risesL (M:Stage)(G:Gauge):1≤ crestP M G:= one_le_mul_of_one_le_of_one_le (Real.one_le_exp M.price_pos.le) (pearls ..)
lemma luteP (M:Stage)(G:Gauge)(d:ℕ) :1≤ lute M G d := by
   apply one_le_mul_of_one_le_of_one_le (Real.one_le_exp _) (Local.atomPrice_ge_one _ _ (zero_le_one.trans (pearls ..))); exact mul_nonneg (add_nonneg M.price_pos.le zero_le_two) (by positivity)
lemma costGood (s:Sheet G)(D:Rolls s)(j i d:ℕ): 0 < costP s D j i d:=div_pos (Doors.rate_pos _) (zero_lt_one.trans_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (orbitCost_one_le _) (luteP ..)) (risesL ..)))
lemma mature (s0:Stage) :0< Push.Local.turnCost s0.order s0.power:=pow_pos (by positivity) _
variable {T:Metals G} {P: Rolls T.p} {A:Alloy T P} {m n d:ℕ}
local notation "i"=> A.B.a.clock.J m
local notation "j"=> A.B.a.clock.J (m+1)
local notation "Z"=> T.p.profile i
local notation "V'"=> T.p.profile j
local notation "B"=> A.B.a.budget m
set_option quotPrecheck false
local notation "Φ"=> Local.factor (hol G) (localSection G d) (B).supportExponent (authors A.B.a m)
local notation "u"=> Motion.orbitCost ((Labels.frames G).level d)
local notation "t!"=> costP T.p P j i d
local notation "P₁"=> crestP V' G
local notation "v0"=> Doors.rate (P.L j)
open Next.Foundations
lemma topL : Φ=lute Z G d:=by unfold authors; rw [params_eq A.B.valid m]; rw [show (B).supportExponent=(Z).supportExponent from Rain.jersey (A:=A) (m:=m)|>.2.2.1];rfl
lemma topsS : t!>0 ∧ u*Φ*(t! *P₁)=v0:=by
   refine ⟨costGood ..,?_⟩;rw [topL]; unfold costP tipsH;field_simp [(zero_lt_one.trans_le (luteP ..)).ne', (zero_lt_one.trans_le (pearls ..)).ne', (zero_lt_one.trans_le (orbitCost_one_le _)).ne']
end amounts
end YM.PhysicalNext.Repeat.Luna
