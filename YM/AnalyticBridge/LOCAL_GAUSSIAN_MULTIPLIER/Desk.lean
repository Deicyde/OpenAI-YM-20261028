import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ledger


/-!
# Price the *true* step multiplier

Sector and construction data.

Use the χ Allocation from SECTOR_MEASURE,
with its actual profile widths.

We keep
negative/overlap cases: no partition assertion about Plot, and no
replacement of an inactive subtree by another Gaussian.

There is
one kernel for ALL factors.

For fog/meanLog instantiation see deployment.

A sector's tag volume uses *uniform* normalization , with
scaled likelihoods to compensate exactly for StepData's counting-sum.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Next.Fluctuations.Sector
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f}

structure Desk (G : Gauge) (S : StepData c f) where
  tube : Tube G S
  betaHat : ℝ
  W : ℝ
  input : Rep G f
  out : BudgetPoint
  radius : ℝ
  chart : ChartRatio G
  broadCut : Chi
  profile : Chi
  paidW : 0 < W
  paidScale : 0 < fiery G betaHat S.patch.L

namespace Desk
variable (d : Desk G S)
def allocation : Allocation G S d.betaHat d.W := d.profile.profiles G S d.betaHat d.W d.paidW d.paidScale
def g : ℝ := coupling d.input.beta

structure Valid : Prop where
  funds : ∃ B : Teller G, B.Funds S d.tube
  lawful : ∃ σ n Λ δ l : ℝ, d.input.Lawful σ n Λ δ l
  same : Presented.Fits d.tube d.input d.betaHat
  betaPos : 0 < d.input.beta
  coarse : d.out.threshold=temp d.betaHat
  ratio : LocalRatio d.chart
  positive : 0 < d.radius
  charted : 4*d.radius < d.chart.radius

end Desk
variable {d : Desk G S}

/-- Precisions paid in the sector. V is a *field variable* of these
functions; only use them on their actual permitted V's. Completion and
post-mask extensions (when differentiating) have to agree there. -/
structure Spot (d : Desk G S) where
  A : Stores S
  k : S.Choices
  F : Forest S.ratio
  stencils : Stencils S
  C : Config G c → Next.SectorChange.Gaussian.Table (In (G:=G) d.betaHat A F)
  m : Config G c → LinkArray G (Frozen A d.betaHat F) → Prices G (Active A d.betaHat F)
  H : Next.SectorChange.Gaussian.Table (Precision.Key F G)

namespace Spot
variable (u : Spot d)

abbrev ActiveKey := Active u.A d.betaHat u.F
abbrev FrozenKey := Frozen u.A d.betaHat u.F
abbrev InKey := In (G:=G) d.betaHat u.A u.F
abbrev Visual := LinkArray G u.FrozenKey × Prices G u.ActiveKey
abbrev Event := Config G c → u.Visual → ℝ

def Flags (V : Config G c) := u.A.flags = RG.flags (temp d.betaHat) V

def variance (V : Config G c) : Measure u.Visual :=
    (piHaar G u.FrozenKey).prod (cloud (u.C V))
instance (V : Config G c) : IsProbabilityMeasure (u.variance V) := by unfold variance; infer_instance

def hard (V : Config G c) (p : u.Visual) : Config G f :=
    physical u.A u.F V p.1 (displaced (u.m V p.1) d.g p.2)

/-- Affine precision from the **same** stencils. -/
def shiftGram (V : Config G c) : Next.SectorChange.Gaussian.Table u.InKey :=
    Rows.gram d.tube d.betaHat V u.k u.stencils u.A u.F

def Available (V : Config G c) := Licenses d.tube d.betaHat V u.k u.A d.input u.stencils u.F d.allocation
  d.broadCut d.chart d.radius (u.C V) (u.m V)

structure Clearing (V : Config G c) : Prop where
  flags : u.Flags V
  kernel : (u.C V).PosDef
  gram : (u.shiftGram V).PosDef
  reference : u.H.PosDef
  available : u.Available V

/-- The price pairing of these **two** logs (E looks at A vs Aflat,
then I+S). Written even in discarded/zero sectors; taking any meaning
from a log here requires the checks. -/
def receipt (V : Config G c) : ℝ :=
    -(Fintype.card u.FrozenKey:ℝ)*Real.log (spare d.chart d.input.beta) -
      (1/2)*(Real.log (u.shiftGram V).det-Real.log u.H.det) +
      (1/2)*Real.log (1+(u.shiftGram V*u.C V-1)).det






def charge (V : Config G c) : ℝ := sieve d.tube d.input.beta d.betaHat V *
    ∫ a, d.allocation.portion u.A u.F V (fun k a => exposed d.input (till d.betaHat) (u.F.drape a) *
      enters d.tube d.input.beta d.betaHat k V (u.F.drape a)) u.k a∂u.F.order G








end Spot
end YM.AnalyticBridge.LocalGaussian
