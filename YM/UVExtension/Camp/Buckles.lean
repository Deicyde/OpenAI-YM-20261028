import YM.UVExtension.Spire.Spark
import YM.UVExtension.Reward.Lights

/-!
# Fixed horizon stabilization criterion for the deterministic recursion.

Absolute Arrives test. Only accepts along step's linear real workspace. Final membrane valuation MUST be on
literally numbered packet lists in the project syntax (varied E paths.
ancestry). No convergence test in infinite-volume order. -- interface to step estimate.
As in construction V real slice-parameters valid everywhere picked; fixed
readings normalized at same currency.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
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
open Oriel Oriel.Charted Guild Tabernacle Above Spire Spire.Fitted Dales Camp.Cart
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A}
    {hG:G.Simple}(S: Uses R hG)
local notation "T!"=> A.B.a
local notation "CST"=> S.grove.pledge

def drawerE (b m n : ℕ) (x: (S.fits b n).Home m) := (place T! m n ((S.fits b n).W m) x).val
abbrev Chest (m n:ℕ)(x:ℕ):= (S.fits x n).Home m
abbrev WordsI (m n:ℕ):= ∀ x, Chest S m n x
abbrev chestR (b : ℕ→ℝ) (m n : ℕ)(x : WordsI S (m+1) n)(N:ℕ) := Reality T! (m+1) n ((S.fits N n).W (m+1)) (x N) (b N)
def compass (b : ℕ→ℝ)(m n:ℕ)(x : WordsI S (m+1) n): ℕ→ℝ:= fun i=> if hi : m < i then Tour.claim R ((S.fits i n).charts m hi) _ (x i) (b i) else 0
def wood (b : ℕ→ℝ)(m n:ℕ)(x:WordsI S (m+1) n) : WordsI S m n:= fun i=> if hi : m < i then Tour.choiceV R hG CST ((S.fits i n).charts m hi) _ ((S.fits i n).shirts m hi) (x i) (b i) else 0
structure Sign : Prop where
    stamps (m n:ℕ) (b:ℕ→ℝ)(x:WordsI S (m+1) n): (∀ᶠ i in atTop,chestR S b m n x i)→ Arrives b → Arrives (fun i=> drawerE S i (m+1) n (x i))→ Arrives (compass S b m n x)∧ Arrives (fun i=> drawerE S i m n (wood S b m n x i))

lemma trim {Z: Type*} [MetricSpace Z][CompleteSpace Z] {f:ℕ→ Z}(he:∀ ε:ℝ,0<ε →∃ g:ℕ→Z, Arrives g ∧ ∀ᶠ i in atTop, dist (f i) (g i)≤ ε): Arrives f:=by
   apply cauchySeq_tendsto_of_complete; rw [Metric.cauchySeq_iff]
   intro ε h; obtain ⟨g,⟨y,hg⟩,hx⟩:= he (ε/4) (by positivity)
   obtain ⟨i,hi⟩:= eventually_atTop.mp (hx.and (hg.eventually (ball_mem_nhds y (by positivity : 0 < ε/4))))
   refine ⟨i, fun j hj k hk=>?_⟩
   obtain ⟨h1,h2⟩:= hi _ hj; obtain ⟨h3,h4⟩:= hi _ hk
   exact (dist_triangle (f j) y (f k)).trans_lt (by rw [dist_comm y]; linarith only [dist_triangle (f j) (g j) y,dist_triangle (f k) (g k) y,h1,h3,mem_ball.mp h2,mem_ball.mp h4])
variable (n:ℕ)(H : Sign S) (w:∀ b, PlotN b) (hp:∀ b:ℕ,w b∈Harbor b)(ht:∀ b, Light b (w b))
-- coordinate arrives test; short nonissue arbitrary

def emit (N:ℕ)(z:PlotN N)(i:ℕ):ℂ:= if h:i≤N then node N z i h else 0
def Charting (w:∀ b,PlotN b) : Prop:=∀ i:ℕ,Arrives fun k=> emit k (w k) i
abbrev centers (_S:Uses R hG) (m:ℕ)(i:ℕ):= faceV (R:=R) (w i) m
variable (hw:Charting w) (hC : Reward.Ends A.B.a A.B.kin.path A.B.kin.alpha)
include hw hC
lemma ratings (m:ℕ) : Arrives (centers w S m):= by
   have h: Arrives (fun k=> Camp.slope T! (A.B.kin.alpha k) m):= by
     let f k:= ∑ j∈Finset.range m,A.B.kin.alpha k j
     have h: Arrives f:= Arrives.sum _ (fun j hj=> hC.prices j)
     exact h.post (T:=fun x=> A.B.a.clock.bar-x) (continuous_const.sub continuous_id)
   let v k:= art (A.B.a.clock.hatBeta m) (Camp.slope T! (A.B.kin.alpha k) m) (Complex.re (emit k (w k) m)); have hp: Arrives v:= (h.pair (hw m)).post (T:=fun z=> Dales.art (A.B.a.clock.hatBeta m) z.1 z.2.re) (by unfold art; fun_prop)
   refine hp.copy ?_; filter_upwards [eventually_ge_atTop m] with k ht; unfold centers faceV v emit; rw [dif_pos ht,dif_pos ht]; rfl

end YM.UVExtension.Camp
