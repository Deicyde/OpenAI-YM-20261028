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
import YM.Work.A05.Read

/-!
# Non-vacuity check in the statement's scope

The RSetup/RAuthors construction is universal (also for zero-dimensional
and/or disconnected gauge images, `Simple` not needed for that part).
Check the genuine nonabelian setting in this representation-based interface.
This file is not an alternative realization of any of the producers: it's a
concrete example where the inputs are meaningful, in particular the
hypothesis of `CLOSED` about the Lie algebra in this convention really
holds. No claims about the rest of the physical premises.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Foundations

open scoped Topology Matrix.Norms.Frobenius BigOperators
open Function Filter NormedSpace

/-- The defining-representation group SU(2), det one in U(2). -/
def SUtwo : Gauge where
  n := 1
  imageGroup := {
    carrier := {X | X.val.det = 1}
    one_mem' := Matrix.det_one
    mul_mem' {X Y} hx hy := by
      change (X.val * Y.val).det = 1
      rw [Matrix.det_mul, hx, hy, mul_one]
    inv_mem' {X} hx := by
      change (star X.val).det = 1
      rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hx, star_one] }
  closed_imageGroup := isClosed_eq (show Continuous fun X : GaugeU 1 => X.val.det from by fun_prop)
    continuous_const

private abbrev M := Matrix (Fin 2) (Fin 2) ℂ

















end YM.Next.Foundations
