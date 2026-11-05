import YM.AnalyticNext.CUBIC_MATCH.Motions
import YM.Next.BOUNDARY.Coordinates
import YM.Next.SCHEDULE.Blocks

set_option warningAsError false

/-!
# Which curve to evaluate

Pass from the possibly large tree tangent to the `A0` profile. Important:
this gauge shift includes root motion. Our calculation of `noiseTaylor` must
then use a compensating change of the coarse input to the penalty. This is a
version of  for cubic only, without introducing all the
centering second-order coordinates. In effect, in the rooted scheme add a
coarse gauge variable whose *first* order is `fixRoot U`. Higher pieces of
that variable won't be needed. No error per site or volume incurred by this
gauge comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open RG Precision Lattice Wilson Exterior Bid Function Filter Matrix Tree Work.F03 Work.F05
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {c f : Side}

/-- Additive fine trial, literal real periodized operator in application. -/
def profile (U : Matrix (Body 1 f) (Body 1 c) ℝ) (x : Dir G c) : Dir G f :=
  fun i => WithLp.toLp 2 (fun j => (U *ᵥ parts G 1 x j) i)

/-- `ψ` profile in E. -/
def psi (S : StepData c f) (x : Dir G f) : fieldDir G c 0 :=
    fun i => WithLp.toLp 2 (fun j => (fixRoot S *ᵥ parts G 1 x j) i)

variable {S : StepData c f} {t : S.Choices} {p : Clip} {P : PathData G}
  (B : Forest S.ratio) (U : Matrix (Body 1 f) (Body 1 c) ℝ)







/-- Compensating coarse inputs to evaluate the original objective. The
sign in `rootTurn` is minus, and this uses `ψ` (not `-ψ`). -/
def compensation (S : StepData c f) (x : Dir G c) (u : Dir G f) (s : ℝ) : Config G c :=
    gauge (rootTurn (psi S u) s) (represent (s • x))




end YM.CubicMatch
