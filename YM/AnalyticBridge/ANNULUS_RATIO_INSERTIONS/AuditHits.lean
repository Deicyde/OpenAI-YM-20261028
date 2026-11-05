import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Station


/-!
# Anchored procurement, including variant tolls

Even on a shared or sector-specific (probability) Gaussian law, compatible
for one step with actual packet products & LFR payment. Include variant
weights and cofactor allowance, AFTER all the post-L quotes paid. Weight
consumer uses an Ac cover price & mandatory alphabet convention from
`ABSOLUTE_SUMS`. No inference of summability over all allocated histories
(tags/K/storage) from its purely geometric count. Explicit premise for
summing variants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Atlas
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations Next.Fluctuations.Sector
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented LabelSum
open SectorNext.Remainder SectorNext.Remainder.Affine Harvest Dress FS Push.AbsoluteSums Push.AbsoluteSums.Packets  Portfolio
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Collection of analytic inputs at the same Teller/height but
with varying sector invocation. A variant may need MANY additional
labels and supports; nothing here is a concession for them. In addition
to a point bound for any companions one also pays for the number of
variants requested at any one compulsory support. Doesn't identify
weights across calls. -/
structure Variant (S : StepData c f) (T : Tube G S) (x : ℝ) where
  chart : Rep G f
  output : Config G c
  stores : Stores S
  owner : Stores S
  trees : Forest S.ratio
  allocation : Chi
  choice : S.Choices
  luggage : Finset ℕ

variable (T : Tube G S) (x w d : ℝ) (J : ChartRatio G)
  (D R R' : ℕ)
namespace Variant
variable (i : Variant S T x)



def law := (piHaar G (Frozen i.stores x i.trees)).prod (cloud (fog i.stores i.trees T x i.output i.choice))

instance : IsProbabilityMeasure (i.law T x) := by unfold law; infer_instance




end Variant

variable {T x w} {P : Teller G} {K E η L κ e' : ℝ} {l n R R' D : ℕ} {N : Side}
  (hJ : LocalRatio J) (hT : P.Funds S T) (hP : Rates P N l D n w K E η L κ e' x J)
  (he : S.patch.L=N) (hx : 100*(1+radiusB x)≤c.val)
  (hD : d=K*fiery G x N)
  (hR : Mooring D l x R R') (hn : 4≤n)

include hJ hT hP he hx hD hR hn





omit hJ hT hP he hx hD hR hn


end YM.AnalyticBridge.AnnulusRatioInsertions.Atlas
