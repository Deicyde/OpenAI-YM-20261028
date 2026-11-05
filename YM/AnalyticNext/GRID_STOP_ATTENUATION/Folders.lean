import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Bid.Craft
import YM.Bid.Fuels
import YM.Next.MULTISOURCE.Bulk
import YM.Next.MULTISOURCE.Split
import YM.Org.Phase
import YM.Org.Theatre
import YM.Work.A05.Read
import YM.Work.A07


set_option warningAsError false

/-!
# From rooted bills to the simultaneous census costs

Folders used in compilation of a physical fork (an `Overlay.Bands`, e.g.
from `GridApprox.Birth`) to the alphabet for `Multi.move_book`.
No enumeration-position cost or Fintype price is introduced *in the budget*.
The period and arity can grow. Provenance data for continuing beyond this
alphabet might still be needed by the red one-step estimate; don't infer them
from the compression.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Compile
open Function Finset RG Lattice Wilson Marker Overlay Multi
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

section folder
variable {V I : Type} [DecidableEq V] {R : Census V}

/-- One bill: cost paid by incidence at each root. -/
structure Folder (u : I → R.Mode) (f : I → ℝ) (w : V → ℝ) (c : ℝ) : Prop where
  nonempty (j : I) : (u j).val.Nonempty
  positive (i : V) : 0 < w i
  nonneg (j : I) : 0 ≤ f j
  root (i : V) : SumBudget (fun j => if i∈ (u j).val then Poly.toll w (u j)*f j else 0) c

def slice (u : I → R.Mode) (f : I → ℝ) (x : Hot R) (i : I) := if u i=x.val then f i else 0
def file (u : I → R.Mode) (f : I → ℝ) (x : Hot R) := ∑' i, slice u f x i

namespace Folder
variable {u : I → R.Mode} {f : I → ℝ} {w : V → ℝ} {c : ℝ}
variable (H : Folder u f w c)
include H

lemma slice_nonneg (x : Hot R) (i : I) : 0 ≤ slice u f x i := by
  unfold slice; split <;> first | exact H.nonneg _ | exact le_rfl

lemma cut (x : Hot R) (d : V) (hd : d ∈ x.sites) :
    SumBudget (fun i => Poly.toll w x.val * slice u f x i) c := by
  refine Multi.permit_le (H.root d) le_rfl fun i => ⟨mul_nonneg (Poly.worth H.positive _).le
    (H.slice_nonneg ..),?_⟩
  by_cases he : u i=x.val
  · change d∈ x.val.val at hd; simp [slice,he,hd]
  simp only [slice,if_neg he,mul_zero]; exact (H.root d).1 i

lemma slice_series (x : Hot R) : Summable (slice u f x) := by
  obtain ⟨i,hi⟩ := x.property
  have he := (H.cut x i hi).2.1.mul_left ((Poly.toll w x.val)⁻¹)
  simpa only [← mul_assoc, inv_mul_cancel₀ (Poly.worth H.positive _).ne',one_mul] using he



lemma file_nonneg (x : Hot R) : 0 ≤ file u f x := tsum_nonneg (H.slice_nonneg x)


end Folder
end folder
end YM.AnalyticNext.GridStop.Compile
