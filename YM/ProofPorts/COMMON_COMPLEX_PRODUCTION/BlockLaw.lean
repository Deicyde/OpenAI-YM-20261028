import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import YM.MultiNext.VACUUM_STABILITY.Holding.Offers
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Blocks
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.PRICE_COMPILER.Post
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian

/-!
# Common Gaussian and argument factorization, with support-dependent spaces

Cf. `Gauss.blocked` at a fixed common padded size. Don't pad the actual
argument systems in integration estimates (risk of an unintended large
dimension in a score): work on each true sublist or linearly observed
subspace, and allow the ambient covariance and all marginal choices to
vary under the tags/frozen links. A block covariance statement on the WHOLE
observed family is required. No independence assumed on joint trigger,
optional or held arguments within a block, including in norm integrals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction
open Function Filter Finset Matrix Lattice RG Wilson Precision Multi.Vacuum Next.SectorChange
open MeasureTheory ProbabilityTheory Gaussian Gauss
open scoped Topology BigOperators Classical MatrixOrder

variable {I J K : Type} [Fintype I] [Fintype K] {D : K→Type} [∀ i,Fintype (D i)]











@[fun_prop] lemma measurable_matVec {X Y : Type} [Fintype Y] (A : Matrix X Y ℝ) : Measurable (A *ᵥ ·) := by
  unfold Matrix.mulVec dotProduct; fun_prop

-- varying tables under the same tags allowed too
@[fun_prop] lemma matVec_varies {W X Y : Type} [MeasurableSpace W] [Fintype Y] {q : W → Matrix X Y ℝ} {v : W→Vec Y}
    (hq : ∀ i j, Measurable (fun w => q w i j)) (hv : Measurable v) : Measurable (fun w => q w *ᵥ v w) := by
  unfold Matrix.mulVec dotProduct; fun_prop (disch := assumption)



-- mixed probability contexts pushed forward; helper for reimbursements, even with `s=∅`.



end YM.ProofPorts.CommonComplexProduction
