import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Yield


/-!
# Physical input for broad chart protection

Not requiring z remains in every ex-charge window. Show from caller weak β and rank schedules.
Volume parameter x and Sparse labels unchanged. Needed *before* taking E current.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Cab
open Function Lattice RG Precision Wilson Pressure Pressure.Stores MeasureTheory
open Matrix Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Tree Next.Fluctuations Filter Win Win.Promise Finset
open Centered Aff Aff.Mint Wages Jewels  
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {x W : ℝ}
    {A : Stores S} {F : Forest S.ratio}



-- pre-authorizations jointly within x tier. Any D,W chosen at their level first.
structure Guest (S : StepData c f) (T : Tube G S) (x W C r : ℝ) : Prop where
  hot : 0 < chartSize G S.patch x
  postal : 4*chartSize G S.patch x < r
  sails : 0 < fiery G x S.patch.L
  walls : ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c), cert S x A V →
    ∀ (U : Config G f) (k : S.Choices), SliceSet S F U → Alive S U k → Seeded A U k V x W →
      ∀ i∈activeB A F (radiusB x), let v := U i*(replica S.ratio V i)⁻¹
      v∈G.lieExp '' Metric.ball 0 r ∧ ‖LocalH.snap G v‖ ≤ chartSize G S.patch x
  lane : Bid.LaneCounts T.up x (fiery G x S.patch.L) T.high C 1 S.ratio.parent






end YM.AnalyticNext.ConnectedActivity.Cab
