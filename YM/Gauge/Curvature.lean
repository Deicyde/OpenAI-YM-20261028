import YM.Gauge.Colors

/-!
Euclidean candidate . Conjugation, bounds and leading jet for the actual projection.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Gauge

open NormedSpace
open scoped Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] frobInner
variable (G : Gauge)

def conjugateL (u : G.El) : G.Mat →ₗᵢ[ℝ] G.Mat where
  toFun := G.conjugate u
  map_add' := by simp [conjugate, mul_add, add_mul]
  map_smul' := by simp [conjugate]
  norm_map' A := by
    change ‖G.mat u * A * star (G.mat u)‖ = _
    rw [frob_mul_eq, mul_frob_eq]
    · simp
    · simp

@[simp] theorem conjugateL_act (u : G.El) (A : G.Mat) : G.conjugateL u A = G.conjugate u A := rfl

@[simp] theorem conjugate_inv (u : G.El) (A : G.Mat) :
    G.conjugate u (G.conjugate u⁻¹ A) = A := by
  simp only [conjugate, mat_inv, star_star]
  calc
    _ = (G.mat u * star (G.mat u)) * A * (G.mat u * star (G.mat u)) := by simp only [mul_assoc]
    _ = A := by simp

theorem project_conjugate (u : G.El) (A : G.Mat) :
    G.projectColor (G.conjugate u A) = G.adjoint u (G.projectColor A) := by
  apply G.colorMat_injective
  rw [colorMat_project, mat_adjoint, colorMat_project]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (G.conjugate_mem u (G.colorMat_project _ ▸ G.colorMat_mem (G.projectColor A)))
  intro w hw
  have e : inner ℝ ((G.conjugateL u) (A - G.lie.starProjection A))
      ((G.conjugateL u) (G.conjugate u⁻¹ w)) = 0 := by
    rw [(G.conjugateL u).inner_map_map]
    exact Submodule.starProjection_inner_eq_zero _ _ (G.conjugate_mem u⁻¹ hw)
  rw [map_sub, conjugateL_act, conjugateL_act, conjugateL_act, G.conjugate_inv] at e
  exact e

@[simp] theorem curvature_unit : G.curvature 1 = 0 := by simp [curvature]

@[fun_prop] theorem continuous_curvature : Continuous G.curvature :=
  G.projectColor.continuous_of_finiteDimensional.comp
    ((G.continuous_mat.sub (G.continuous_mat.comp continuous_inv)).const_smul (1/2 : ℝ))

theorem curvature_conjugate (u v : G.El) :
    G.curvature (u*v*u⁻¹) = G.adjoint u (G.curvature v) := by
  unfold curvature
  rw [← G.project_conjugate]
  simp only [mat_inv, mat_mul, conjugate, star_mul, star_star]
  simp only [mul_smul_comm, mul_sub, sub_mul, smul_mul_assoc, mul_assoc]

theorem curvature_norm (u : G.El) : ‖G.curvature u‖ ≤ G.chord u := by
  calc
    ‖G.curvature u‖ ≤ ‖(1/2 : ℝ) • (G.mat u - G.mat u⁻¹)‖ / G.colorScale :=
      G.project_norm _
    _ = (1/2 : ℝ) * ‖G.mat u - G.mat u⁻¹‖ / G.colorScale := by
      rw [norm_smul, Real.norm_of_nonneg]; norm_num
    _ ≤ (1/2 : ℝ) * (‖G.mat u - 1‖ + ‖G.mat u⁻¹ - 1‖) / G.colorScale := by
      have ht : ‖G.mat u - G.mat u⁻¹‖ ≤ ‖G.mat u - 1‖ + ‖G.mat u⁻¹ - 1‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
        exact dist_triangle_right _ _ _
      have hn := G.colorScale_pos
      gcongr
    _ = (G.chord u + G.chord u⁻¹) / 2 := by unfold chord colorScale; ring
    _ = G.chord u := by rw [G.chord_inv]; ring

/-- First variation with the actual normalization. -/
theorem leading_curvature (c : G.Color) :
    HasDerivAt (fun t : ℝ => G.curvature (G.lieExp (t • c))) c 0 := by
  let A := fun t : ℝ => G.mat (G.lieExp (t • c))
  have hA : HasDerivAt A (G.colorMat c) 0 := by
    unfold A
    simp only [G.mat_lieExp, map_smul]
    simpa using! hasDerivAt_exp_smul_const (G.colorMat c) (0 : ℝ)
  let P : ℝ → G.Mat := fun t => (1/2 : ℝ) • (A t - star (A t))
  have hB : HasDerivAt P (G.colorMat c) 0 := by
    have ht := (hA.sub hA.star).const_smul (1/2 : ℝ)
    rw [colorMat_skew, sub_neg_eq_add, ← two_smul ℝ, smul_smul,
      div_mul_cancel₀ _ (two_ne_zero), one_smul] at ht
    exact ht
  simp_rw [curvature, mat_inv]
  have hi :=
    (G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hB)
  change HasDerivAt (fun x ↦ G.projectColor (P x)) (G.projectColor (G.colorMat c)) 0 at hi
  rw [G.project_colorMat] at hi
  exact hi

end YM.Gauge
