import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Press
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bore
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stamped


/-!
# Before Wake: common post-L preparation of all steps

Pass this height BEFORE consuming a trajectory. Includes genuine φ/J
use with arbitrary frozen allocation via exact Licenses, the fixed order chart
and marginal price, and all disqualifications. Doesn't buy the
mark/trace/Schur jet tables or final coefficient bills. For those use separate
derivative currencies and Wakes proofs. All with the SAME actual covariance.
Do not smuggle changing it to a tail-truncated field on optional selections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Matrix Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Schur YM.Next.Fluctuations.Sector
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f}
namespace Peak
variable {I : Type} [Fintype I] [DecidableEq I] {A C : Matrix I I ℝ} {ρ η : ℝ} {a : I → Site c}





omit [DecidableEq I] in
lemma mono {c : ℝ} (h : Peak A c) (hv : c ≤ ρ) : Peak A ρ :=
  fun v => (h v).trans (mul_le_mul_of_nonneg_right hv (YM.FreeResolvent.normSum_nn _))
end Peak

/-- The sector called by Service. Don't pass to a horizon/pricing-table
identity in which the matrix can be a different prescription. Native
comparator SOME true kinetic on its **own** H (can separately identify
that extensive price when feeds match and symmetry paid). -/
def spectacle (d : Desk G S) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) : Spot d :=
    ⟨A,k,F,shots S d.betaHat,fun V => fog A F d.tube d.betaHat V k,fun V => meanLog A F d.tube d.betaHat V k d.broadCut d.radius,
      Native.kinetic d.tube F k d.betaHat⟩

/-- Actual second-stage requirements. -/
structure Provision (d : Desk G S) (P : Teller G) (L Q r : ℝ) (k : ℕ) : Prop where
  funded : P.Funds S d.tube
  lawful : d.Valid
  surveys : ∀ (A : Stores S) (F : Forest S.ratio) (t : S.Choices),
    let B := spectacle d A F t
    ∀ V, B.Flags V → B.Clearing V ∧
      Admitted A F d.betaHat V t d.chart d.allocation d.radius ∧ Peak (B.C V) Q
  allCases : Curtain.Ready d.chart d.g r
  allow : 2*d.radius < r
  jacob : ∃ L W, Studio d.chart r k L W
  power : ∀ x,Farewell (fun y : G.Color => logGuard d.broadCut d.chart d.radius (d.radius • y)) x k (L*d.radius^2)


end YM.AnalyticBridge.LocalGaussian
