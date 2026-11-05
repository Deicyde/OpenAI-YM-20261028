import YM.Push.LOOP_COEFFICIENT.Pullback
import YM.Work.F02.Path

/-!
# Lie matrices on continued color coordinates, with physical normalization
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Matrix Function Set Filter Metric Lattice Laurent RG Bloch Work.F02 Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

def complexLie (G : Gauge) : CColor G →L[ℂ] G.Mat := LinearMap.toContinuousLinearMap (∑ i, (LinearMap.proj i).smulRight (G.colorMat (EuclideanSpace.basisFun G.ColorIndex ℝ i)))

lemma complexLie_real (v : G.Color) : complexLie G (colorUp G v) = G.colorMat v := by
  unfold complexLie; rw [LinearMap.coe_toContinuousLinearMap', LinearMap.sum_apply]
  conv_rhs => rw [← (EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr v]
  simp [colorUp_apply]



def liePair (G : Gauge) := (LinearMap.mul ℂ G.Mat).compl₁₂ (complexLie G).toLinearMap (complexLie G).toLinearMap

def cAd (G : Gauge) := ((liePair G)-(liePair G).flip).compr₂ (colorProject G).toLinearMap





def cDot (G : Gauge) : CColor G →ₗ[ℂ] CColor G →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ dotProduct add_dotProduct (fun _ => smul_dotProduct _) dotProduct_add (fun _ => dotProduct_smul _)
lemma color_dot (x y : G.Color) : colorUp G x ⬝ᵥ colorUp G y = (inner ℝ x y : ℝ) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,colorUp_apply, ofReal_sum,ofReal_mul]; exact Finset.sum_congr rfl (fun i _ => mul_comm ..)


end YM.Push.Loops.Paths
