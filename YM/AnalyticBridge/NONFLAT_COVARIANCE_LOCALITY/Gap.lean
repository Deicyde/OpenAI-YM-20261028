import Mathlib.Data.Set.Finite.List
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Chart
import YM.Push.FREE_RESOLVENT.Polar
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Remainder
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils

/-!
# Positivity in the actual chart neighborhoods

Use genuine sector geometry for the base gap (see SectorChange.Gap).
A formal sector over *correct recorded output flags* suffices there. The
neighborhood in which the jets can be priced is affording around such V
(per `branch_inputs`); estimate the persistence of the gap in that **same**
neighborhood with possibly smaller radius, sector A and forest/trunks and
input coordinates UNCHANGED. No need for probabilistic smallness of the off-mask
data nor comparison to a globally ungauged flat Hessian. Direction evaluation
and counting metrics not conflated -- don't take an ambient Frobenius norm
bound per patch to conclude a volume-uniform continuity statement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Matrix Function Filter Metric Set
open Lattice RG Wilson Pressure Tree
open Next.SectorChange 
open FreeResolvent Mark TestD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side}

section math
variable {α : Type} [Fintype α]
    {F : Coord G c → Matrix α α ℝ} {s C r η : ℝ}




-- Evaluate on the whole Coord norm ball while keeping exponential decay.


-- fderiv of actual counting quadratic form, not paying any card factor
private def energy (b : α → ℝ) : Matrix α α ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ({
    toFun M := b ⬝ᵥ (M *ᵥ b)
    map_add' M N := by rw [Matrix.add_mulVec,dotProduct_add]
    map_smul' t M := by simp only [Matrix.smul_mulVec,dotProduct_smul,RingHom.id_apply] } :
    Matrix α α ℝ →ₗ[ℝ] ℝ)


end math

/-- Real Gram on SC.Active and all its color components, fixed even off the
indicator. -/
def precision {S : StepData c f} (x : ℝ) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (k : S.Choices) (T : Tube G S) (z : Coord G c) :=
  Rows.gram T x (coarse V z) k (shots S x) A F

lemma precision_symm {S : StepData c f} (x : ℝ) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (k : S.Choices) (T : Tube G S) (z : Coord G c) :
    (precision x A F V k T z).IsSymm := by
  unfold precision Rows.gram Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]



end YM.AnalyticBridge.NonflatCovarianceLocality
