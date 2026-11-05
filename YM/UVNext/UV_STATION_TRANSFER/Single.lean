import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.UVNext.UV_STATION_TRANSFER.Columns
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04



set_option warningAsError false

/-!
# Geometry B, from k-grid replication of one column at the origin

At the link sizes (actual level sides)
in our input, it suffices for both slab and uncentered bulk applications
to supply estimates on the fields centered at zero, even with no other
offsets and only on one basis: prove explicitly using the law symmetries
and already available cutoff reflection tools.

Applies even where the chosen
complex basis is not a signed or real multiplet.

No change of column at other
offsets.

We use ONE common cost (per arity etc) renormalized upwards to pay
all the column transformations in the finite list.

No invoking Estimates
with variable precisions downstream as though inferring uniformity there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.StationTransfer.Ticket
open Function Set Filter MeasureTheory Metric Analysis Extraction
open Lattice Wilson Cells Climb Ward Table Next.UVStress Marker Stock
open Extraction.Spin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {D : ℕ}
variable (T : Ticket C D)









lemma permit_from {n} (v : Fin n → C.book.Token) {Q : ℝ} {k N p : ℕ}
    (hA : ∀ i j, centeredBudget C (token C.book (v i) j) Q k N p) : Difference.Permit v Q k N p := by
  rintro i w (rfl|⟨a,rfl⟩)
  · simpa using hA i (1,false)
  simpa only [token, if_true, Bool.true_eq, Spin.swapC, ← Register.token_adjoint] using hA i (Signed.mirror a,true)



end YM.UVNext.StationTransfer.Ticket
