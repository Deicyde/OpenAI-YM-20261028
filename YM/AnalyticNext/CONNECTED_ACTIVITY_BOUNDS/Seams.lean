import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Hyssop

/-!
# Stencils of Booth letters and estimates

Per operational request, so use P meeting purchases to test actual paths.
Check reductions by orientation with same θ. Show shell dependencies and D,N gates
as genuinely local despite summation orders and wrap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Coverage.Shed
open Function Lattice RG Precision Wilson Pressure Pressure.Stores MeasureTheory Push.SectorMeasure
open Matrix Push.SectorMeasure.Oriented Push.AbsoluteSums Tree Next.Fluctuations Filter Win Win.Promise Finset
open Centered Aff Aff.Mint Wages Jewels   Mixed Work.E03 Exterior Bloch
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S}

lemma roll_fine (U V : Config G f) (x : Site c) (s : Signed) (D : ℕ) (h : AgreeNear S.ratio.parent (s.act x) (D+1) U V) :
    AgreeNear S.ratio.parent x D (pull s 0 U) (pull s 0 V) :=
    pull_agreesFine S (s,Sum.inr (x,0)) h -- syntax

section Booth
variable {x C : ℝ} {A A' : Stores S} {F : Forest S.ratio} {Y : Mint T F A x} {Y' : Mint T F A' x} {X : Support c}
    (h : Shed F Y Y' X) {P : Teller G} (hT : P.Funds S T) (hC : Optic T x C) {U W : Config G f}
include hC



include h hT

end Booth
end YM.AnalyticNext.ConnectedActivity.Coverage.Shed
