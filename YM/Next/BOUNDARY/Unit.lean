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
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07

/-!
# Normalization of the unit in the realizing field domain

Another physical-label compatibility at the boundary. Do not infer permutation
symmetry of the relativistic correlators; unit readout works even in interior
slots, including in words of arbitrary length, with the original field domain.
Only use test convergence already in `Contour.From`. All integrations use
actual spacetime volumes including empty arity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY
open Set Filter Function MeasureTheory
open Boundary OS Spec Org
open scoped Topology InnerProductSpace BigOperators

variable {G : Gauge} {L : Register G} {n : ℕ}

private def single_out (i : Fin (n+1)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv n).trans (finSuccEquiv' i).symm





variable {S T : Table L}



private def pivot (i : Fin (n+1)) : Points (n+1) ≃ₗᵢ[ℝ] Points (n+1) where
  toFun := Points.rearrange (single_out i)
  invFun := Points.rearrange (single_out i).symm
  left_inv x := by ext1; simp
  right_inv x := by ext1; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    change ‖Points.rearrange (single_out i) x‖=‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2 _ (Points.rearrange _ _),
      PiLp.norm_sq_eq_of_L2 _ x]
    exact Equiv.sum_comp (single_out i) fun j => ‖x j‖^2
















end YM.Next.BOUNDARY
