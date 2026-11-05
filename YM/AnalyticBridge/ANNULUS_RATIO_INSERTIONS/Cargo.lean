import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Package
import YM.Next.FREE_KERNELS.Lifts



/-!
# Simultaneous entry to the annulus payment

Before regrouping. On any Itemized assortment at this sector. Check
correct V case licensed and supply exact recipes incl q-choice and K-list
incidence to the real step computation. Output factors from a product
of joint-Gaussian multipliers can be paid there, or thereafter while
keeping the same G,S,F,A,V,k... and actual prerequisites, without assuming
independence WRT neighboring Y arguments. Further estimates, e.g.
using geometric covariance to deduce independence when portfolios combined
across A's, would require their own proofs, see E ss:gas and corresponding
other B70 WPs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Portfolio
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix Finset
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations Next.Fluctuations.Sector
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented LabelSum
-- avoid reserve/crown
open SectorNext.Remainder.Affine Harvest Dress  
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

variable (A : Stores S) (T : Tube G S) (x w : ℝ) (V : Config G c) (k : S.Choices) (q : Chi)
  (d : ℝ) (J : ChartRatio G) (p : Rep G f) (F : Forest S.ratio)
  (L : Bond f → ℝ) (m : Mean (G:=G) A x F)
  (X : Finset (Stores S)) (D R R' : ℕ) (uniform : Bool) (b : Finset ℕ)

/-- Extract any portfolio of disjoint convention-compatible compulsory packets. -/
def cart (y : GaussArgs (G:=G) A x F) := ∏ i∈X, wrapper i A T x w V k q d J p F L m uniform b D R R' y





end YM.AnalyticBridge.AnnulusRatioInsertions.Portfolio
