import YM.Next.FLUCTUATIONS.Kernel
import YM.Push.FREE_RESOLVENT.Masking
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian


/-!
# Lifting active matrices into FreeResolvent physical coordinates

A single convention for going from the SectorChange integration matrices to
(possibly much larger) full physical matrices. It keeps the literal counting
coordinate, not a quotient by volume/zero modes. Inactive indices included in
an inverse calculation will have to see the shift too.
-/

noncomputable section

namespace YM.AnalyticBridge.GaussianInterior
open Next.SectorChange



namespace Padding
open Function Matrix FreeResolvent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {α β : Type}
variable (e : β ↪ α)

/-- All the other physical positions. -/
abbrev Other := {i : α // i ∉ Set.range e}

def together : (β ⊕ Other e) ≃ α :=
  ((Equiv.ofInjective e e.injective).sumCongr (Equiv.refl _)).trans
    (Equiv.sumCompl (· ∈ Set.range e))

theorem first (i : β) : together e (Sum.inl i) = e i := rfl



section full
variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Entries off the integration coordinates are exactly `w I`; between the
two sets the entries vanish. Use `w=1` for completion of the physical Gram
and for comparison (only!) on padded normals. No new integration-coordinate
or chart charges then. -/
def put (Q : Gaussian.Table β) (w : ℝ) : Gaussian.Table α :=
  insertion e * Q * (insertion e).transpose + w • FreeResolvent.Shell.off e





omit [Fintype α] [DecidableEq β] in
theorem put_transpose (Q : Gaussian.Table β) (w : ℝ) : (put e Q w).transpose = put e Q.transpose w := by
  unfold put
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_mul, Matrix.transpose_smul, FreeResolvent.Shell.undo, Matrix.mul_assoc]







omit [DecidableEq β] in
/-- `Shell.pad` takes an **ambient** matrix as argument. In particular, when
using an unprojected affine precision, project it before inverting. -/
theorem padded (A : Gaussian.Table α) :
    FreeResolvent.Shell.pad e A = put e (A.submatrix e e) 1 := by
  rw [FreeResolvent.Shell.pad, FreeResolvent.Shell.sliced, put, one_smul]













end full
end Padding
end YM.AnalyticBridge.GaussianInterior
