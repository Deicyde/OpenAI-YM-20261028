import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Bolt
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.FeeBook
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Kilns

/-!
# Prices for the **actual** conditional integral

E budget corresponding to eq:prodvv (integrated values, looser rates/caps) for our vocabulary. Price hit
tracks powers price/arity and seed gain, including root vs absolute
behavior. Can be applied to exactly the sectors needed (including
completions only for estimating). Ready with pre-post pricing lemma for
stages of inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Cab
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths Chains Calls Mixed Canvas
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}
  {P : Teller G} {α : Type} [MeasurableSpace α]

section energy
variable (T : Tube G S) (hT : P.Funds S T) (x r W : ℝ) (N : ChartRatio G) (hN : Choice N r)
    (R : Rep G f) {σ C Λ δ w : ℝ} (hR : R.Lawful σ C Λ δ w) (b : Costs) (hb : FeeBook T x W r R N b)
include hT hN hR

lemma shapes {α : Type} [MeasurableSpace α] {f' : α→Config G c} (h : Measurable f') (F : Forest S.ratio)
    (A : Stores S) (k : S.Choices) (H : Chi) (s : Finset (Tab S)) (L : Finset ℕ) {a : α→F.Slice G}
    (he : Measurable a) {z : α→ArrayR G f} (hp : Measurable z) :
    Measurable fun p => payfield T x r W R N A F (f' p) k H s L (a p) (z p) := by
  let Y (p : α) := figure T x r H A F (f' p) k (a p)
  have hb : Bent Y r H k := ⟨h,he,fun p => ⟨rfl,rfl⟩,fun p => ⟨rfl,rfl⟩⟩
  exact Finset.measurable_fun_prod _ fun i _ => hb.treeWalk hN hT R hR W L i hp





include hb


end energy
end YM.AnalyticNext.ConnectedActivity.Cab
