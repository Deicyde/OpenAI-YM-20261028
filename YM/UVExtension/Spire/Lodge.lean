import YM.UVExtension.Dales.Start
import YM.UVExtension.Camp.Minuet
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Spire
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
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    (hG:G.Simple){ε:ℝ}(t:Crest R ε)(u:Paperwork R.shape ε Camp.soft A.delay)
    (hk:Planned.Port.AtTop A.B.kin)(hp:∀ N,Start.Allows A.B.a N)(h:∀ N,Entry A.B.a N soft)(N n:ℕ)
structure Fitted where
    W : ∀ i,Cham A.B.a i n
    start : W N=maiden R hk (hp N) n
    charts i : i<N → Tour R N i n ε
    shirts i (h:i<N):Dales.Tour.Hind R hG t (charts i h) (W (i+1)) (W i)
lemma fitted : Nonempty (Fitted R hG t hk hp N n):= by
   let G':=fun i (hi:i<N) (d:Cham A.B.a (i+1) n)=> Classical.choice (Dales.touring R hi t d)
   let U m (h:m≤N): Cham A.B.a m n:= Nat.decreasingInduction (motive:=fun m _=> Cham A.B.a m n) (fun i hi D=> (G' i hi D).back R hG t D) (maiden R hk (hp N) n) h
   let v m:= if h:m≤N then U m h else maiden R hk (hp m) n
   have he m (h:m≤N): v m= U m h:= dif_pos h; let Z (m:ℕ)(h:m<N):= G' m h (v (m+1))
   refine ⟨⟨v,(he _ le_rfl).trans (Nat.decreasingInduction_self ..),Z,fun i hi=> ⟨?_⟩⟩⟩; unfold Z; rw [he _ hi,he _ hi.le]; exact Nat.decreasingInduction_succ_left _ _ _ _

include hG in
lemma land (i:ℕ)(hi:i≤N) : InsideB (A.B.a.clock.hatBeta i) (Camp.slope A.B.a (A.B.kin.alpha N) i) := by
   exact Camp.planned hG A.B.a (RG.Shoot.Drifting.pay A.B.valid) (fun _ hz=> A.B.support.kinetic _ _ hz) hi

namespace Fitted
-- Factor.Fitted attached
variable {R hG t hk hp N n} (H:Fitted R hG t hk hp N n)
abbrev Hut i:= Hold A.B.a i n (H.W i)
abbrev Center (i:ℕ) := Camp.slope A.B.a (A.B.kin.alpha N) i
-- arguments need H for inference?
abbrev Started (H:Fitted R hG t hk hp N n)(F₀:ℂ×H.Hut N→ H.Hut N) := Dales.Order (d:=H.W N) (clearing R (hp N) hk H.start (Camp.slope A.B.a (A.B.kin.alpha N) N)) soft F₀
abbrev Colored (m:ℕ)(he:m<N)(f:ℂ×H.Hut (m+1) →ℂ) := Dales.Order (d:=H.W (m+1)) (flowing R (H.charts m he) _ (Camp.slope A.B.a (A.B.kin.alpha N) (m+1))) (Yard.rake (A.B.a.clock.hatBeta (m+1))) f
abbrev Gather (m:ℕ)(he:m<N)(f:ℂ×H.Hut (m+1) →H.Hut m) := Dales.Order (d:=H.W (m+1)) (marble R hG t (H.charts m he) _ (H.shirts m he) (Camp.slope A.B.a (A.B.kin.alpha N) (m+1))) soft f
structure Took (V:Cart A.B.a N H.Hut): Prop where
    head : Started H V.headA
    pigment i (he:i<N): Colored H i he (V.gain i he)
    phase i (he:i<N): Gather H i he (V.car i he)
include h u
lemma zesty : ∃ V, H.Took V:=by
   obtain ⟨f,hf⟩:= Dales.born R (hp N) hk H.start (h N) (by norm_num [Camp.soft,rim]) (land (A:=A) hG N N le_rfl)
   have he m (he:m<N) := Dales.shelves R hG t (H.charts m he) (H.W (m+1)) u (land (A:=A) hG N (m+1) he) (H.shirts m he)
   choose F hF using fun m hi=> (he m hi).1; choose G h' using fun m hi=> (he m hi).2
   exact ⟨⟨f,G,F, ⟨hf.bounds.1,hf.bounds.2.1,hf.bounds.2.2⟩, fun i he=> ⟨(h' i he).bounds.1,(h' i he).bounds.2.1,(h' i he).bounds.2.2⟩, fun i he=> ⟨(hF i he).bounds.1,(hF i he).bounds.2.1,(hF i he).bounds.2.2⟩⟩,hf,hF,h'⟩

end Fitted
end YM.UVExtension.Spire
