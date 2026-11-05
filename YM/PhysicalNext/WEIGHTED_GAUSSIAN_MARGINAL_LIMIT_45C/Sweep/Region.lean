import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Venue.Space


/-!
# Every finite list fitting in the region

The purchase of K,degree remains before x. Acquire for ONE test at fixed
degree D; use with D+1 ≤ K. Extends the covariance-marginal comparison to
polynomials (with actual coefficient norm in the bills) even when total
*number of their variables* across terms grows to fill the whole eligible
radius. Preserves coercivity & actual moment bills from the small-corner
step on their exact full data. Do not assume likelihood or joint endpoint
load prices at these large arities. All tags/roll/floors/conventions/choices
same as the original comparison. Applies also to separate, unshifted
curvature fluctuation calculation below. Everything in the gauge of the
old permitting pair.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
open AnalyticBridge.LocalGaussianLaws Venue
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Local
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff ENNReal

variable {tier : ℕ} {G : Gauge} {c f : Side} {S : StepData c f} {H : Bed}
variable {A : Stores S} {T : Tube G S} {o : Site c} {V : Config G c} {x E : ℝ} {D K : ℕ}
variable {F : Forest S.ratio} {t : Site c → G.El} {v : Dir G c}



/-- Largest available list. Need not produce a fresh certificate nor
shrink its label tape across calls. -/
def readers (tier : ℕ) (G : Gauge) (F : Forest S.ratio) (A : Stores S) (x : ℝ) (o : Site c) :=
  (Finset.univ (α:=In x A F (G:=G))).filter fun q => separation o (front A F q) ≤ vista tier x/4





end YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
