import YM.Push.STATIONARY_UNIFORM.Along

/-!
# Full real ball compatibility

Fixed-point neighborhood in each tree, holding all shared choices. Needn't
transform/regauge to get the estimates at one volume from another volume.
But want to know whether the paths really cooperate! Use F05 eventual
switch at origin; *group* relation then extends to the full real horizon
by analyticity on that horizon. Thus values/Jets there can use a translating
choice if paid in any other. For thermal germs also price the radius in the
LocalRatio hypothesis; not claiming positivity of a Hessian determinant off
the slices, or estimates on contour ratios or trace logs. These lemmas are
meant to consume on real branches.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior Bid
open Work.F03  Matrix
open Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {B T : Forest S.ratio} {R : PathData G} {p : Clip}
variable {μ C Λ : ℝ} {n j : ℕ} {Q : KernelChoices} {A : Before G μ C j Q n}
variable {g : In G c → AxisChart G B} {u : In G c → AxisChart G T}
variable {x : Positions (Primary c G)}

def surface (g : In G c → AxisChart G B) (x : Positions (Primary c G)) := lifting B (represent (tint G _ x)) (g (tint G _ x))


namespace Before.Service
variable (hg : A.Service B p R g) (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q)
include hg hp hK hj ht









/-- For any one LocalRatio (chosen before L) stay in its radius too. -/
def heatLimit (G : Gauge) (Y : ChartPrices) (n : ℕ) (P : ChartRatio G) := min Y.horizon (P.radius / (shade G * trailCost Y n))




end Before.Service
end YM.Push.Uniform
