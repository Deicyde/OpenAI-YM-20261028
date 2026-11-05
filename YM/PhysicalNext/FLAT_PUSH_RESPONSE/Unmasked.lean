import Mathlib.MeasureTheory.Measure.Tilted
import YM.Extra.WILSON_STARTUP.Match
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Sieve
import YM.Primitives.SMALL_FIELD_EXTERIOR.Faces
import YM.Push.BETA_TRANSPORT.Gibbs
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.STATIONARY_UNIFORM.Paths

/-!
# Fixed-period unnormalized thermal interpretation for TRUE Wilson step

Negative-log of the actual pushed density, in the prescribed slice-free
coarse field directions. Doesn't assert using only log-sectors without control.
No claim this calculates the Hessian on a match that depends on β; our
limit theorem requires parameters FROZEN (take at the chosen step of a
calendar). On a larger family must provide compatibility with entrance-
delay bounds and ALL Step stability. In particular can't use arbitrary g→0
here for estimating band. Kept as a theorem *with the S, β normalizations*,
earned from exact transfers before estimate. Then deploy to THOSE launch
data (next file).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open Function Filter  Set Metric Asymptotics MeasureTheory Next.SectorChange.Gaussian
open RG Wilson Precision Lattice Push.BetaTransport Pressure Work.F05 Tree Matrix Primitives.SmallFieldExterior
  
open scoped Matrix Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

section diff
variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : Z→ℝ}
private lemma charge (h : ContDiffAt ℝ 2 f 0) (u : Z) : accel (fun t : ℝ=> f (t • u)) 0=
    (iteratedFDeriv ℝ 2 f 0 ![u,u]) := by
  let L : ℝ →L[ℝ] Z := ContinuousLinearMap.toSpanSingleton ℝ u
  have hi : Tendsto L (𝓝 0) (𝓝 0) := by simpa using L.continuous.tendsto 0
  have he : deriv (fun t : ℝ=> f (t • u))=ᶠ[𝓝 0] fun x : ℝ=> fderiv ℝ f (L x) u := by
    filter_upwards [hi.eventually (h.eventually (by norm_num))] with x (he : ContDiffAt ℝ 2 f (L x))
    have hh : HasDerivAt (fun t : ℝ=>t • u) u x := by simpa using (hasDerivAt_id' x).smul_const u
    exact (he.differentiableAt (by norm_num)|>.hasFDerivAt.comp_hasDerivAt x hh).deriv
  unfold accel; rw [he.deriv_eq]
  let D := ContinuousLinearMap.apply ℝ ℝ u
  have hx := D.hasFDerivAt.comp (f:=fderiv ℝ f) 0 ((h.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hz : L 0=0 := map_zero L
  have hv := hx.comp_hasDerivAt_of_eq 0 (L.hasFDerivAt (x:=0)).hasDerivAt hz.symm
  exact hv.deriv.trans (by rw [iteratedFDeriv_two_apply]; change fderiv ℝ (fderiv ℝ f) 0 ((1:ℝ) • u) u=_; rw [one_smul]; rfl)



end diff
variable {G : Gauge} {m n : Side} (S : StepData m n)






variable {S} (B : Forest S.ratio) (k : S.Choices) (u : Bid.Dir G m → AxisChart G B) (p : Clip) (R : PathData G) (w : Bid.Dir G m) {P : ChartRatio G} {r : ℝ}

-- True physical determinant correction at EVERY fixed admissible period.

variable {p R u B}








end YM.PhysicalNext.FlatResponse
