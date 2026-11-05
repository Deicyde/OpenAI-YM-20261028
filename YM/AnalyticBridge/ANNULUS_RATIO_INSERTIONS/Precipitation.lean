import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Cargo
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Parade
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Station
import YM.Push.ABSOLUTE_SUMS.Charge

/-!
# Paying  at the real intake (some letters)

Application of Gala consumer, before reconnecting; joint procurement
on the true dressed calls. Rates and Gala supplied at once.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Parade
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented LabelSum
open Tier Wisps Schur LocalJet Completion
open SectorNext.Remainder SectorNext.Remainder.Affine Harvest Dress
open Portfolio Prism Prism.Breeze Prism.Arc Push.AbsoluteSums.Packets FS
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure

section payment
variable {G : Gauge} {N : Side} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio)
  (k:S.Choices) (V:Config G c) (q:Chi) (d : ℝ) (Z : ChartRatio G)
  (p:Rep G f) (w : ℝ) (X : Finset (Stores S)) (R R' D : ℕ) (b : Finset ℕ) (t : Bool)

def brigade := cart A T x w V k q d Z p F (localPair T A F x V k) (meanLog A F T x V k q d) X D R R' t b

/-- A sufficient condition on any accompaniment, tests only on the
nonzero support of the portfolio, omits pricing w of ratio contacts
which are GENUINELY evaluated in addition. May use as triggers
only those for which the nonzeroness implication holds on this term,
not every ``possibly eligible'' parent. To consume at L4 price instead
use `Prism.Arc.r4` with `Cradled`. -/
structure Embark (P J : Finset (Active A x F)) (i : ℕ) (H ρ : ℝ) (κ : GaussArgs (G:=G) A x F → ℝ) : Prop where
  due : 0 ≤ H
  sale : Measurable (fun y=> brigade T x A F k V q d Z p w X R R' D b t y * κ y)
  value y : brigade T x A F k V q d Z p w X R R' D b t y ≠ 0 → ‖κ y‖ ≤ H*scores P i y.2
  yields y : brigade T x A F k V q d Z p w X R R' D b t y*κ y≠0 → y.2∈triggered J ρ









variable {u v a M H L Θ K θ E : ℝ} {j i : ℕ} {Q : Teller G}
  {n B₀ : ℕ} {ζ B η Y e' : ℝ}
  (hZ:LocalRatio Z) (hT:Q.Funds S T) (hP:Rates Q N B₀ D n w K B η Y ζ e' x Z) (hH : Gala Q N u v a M H L Θ K x θ E j i)
  (hl : S.patch.L=N) (hW : 100*(1+radiusB x)≤c.val) (hV : A.flags=RG.flags (temp x) V)
  (hD : d=K*fiery G x N) (hβ : p.beta∈Set.Icc (Scales.y G N x/2) (2*Scales.y G N x)) (hm:Mooring D B₀ x R R')
  (hn:4≤n) (hc:Itemized A B₀ (radiusB x) X)
include hZ hT hP hH hl hW hV hD hβ hm hn hc


end payment
end YM.AnalyticBridge.AnnulusRatioInsertions.Parade
