import YM.Next.EXTRACTION.Base
import YM.Work.D06

/-!
# Use the normalized base in downstream contracts

Keep the same bin, differential plan, period witnesses and history. This
module does *not* produce corrected detector estimates for `Seed`; it can
receive those on the given `f` (possibly after further refinement). Some
consumers are available already without those estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Extract
open Set Function Filter MeasureTheory Extraction Table Dash OS
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {f : Order} {S T : Table C.book} {M : ℕ → Table C.book}
variable {R : Bin S} {W : DiffPlan T}

lemma Base.seed (H : Base C f S M R T W) (h : Cells.RankWidths C f T) : Spec.Seed C f T :=
  ⟨H.family,H.clean.mesh.integral,H.points,H.kernel,H.center.cells,h⟩

/-- Differential consumers may work with this orientation and the nulls
`Base.null` without any change of bin. -/
lemma Base.oriented (H : Base C f S M R T W) : W.Orientation H.kernel.spin :=
  Work.D06.answer H.family H.clean.smooth H.clean.basic.toSymmetric H.points W H.clean.tilt H.clean.ready H.kernel.spin




end YM.Next.Extract
