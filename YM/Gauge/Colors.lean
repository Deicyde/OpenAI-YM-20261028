import YM.Gauge.Lie
import Mathlib.LinearAlgebra.Trace

/-!
# Physical color coordinates and Lie projection

Colors are **orthonormal for the convention `(-1/d₀) tr (XY)`**
(and using real skew matrices). Work with `ℓ²` on Color. When using `‖ ‖` on Mat
or Alg, use `Matrix.Norms.Frobenius`: this norm on a Lie alg matrix is
`sqrt G.repDim` times the physical one. There is no default real inner product
on matrices exposed as an instance by this module; we use `frobInner` as a local instance.

This fixes a single representation of the group and colors for potential, curvature,
phase and Lorentz arguments. .
-/

set_option autoImplicit false
noncomputable section
namespace YM.Gauge

open Set NormedSpace
open scoped Matrix.Norms.Frobenius InnerProductSpace

/-- Real Frobenius inner product in the defining representation (not normalized). -/
@[instance_reducible]
def frobInner (n : ℕ) : InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℂ) where
  inner x y := (x * star y).trace.re
  norm_sq_eq_re_inner x := frob_sq x
  conj_inner_symm x y := by
    have h (z : Matrix (Fin n) (Fin n) ℂ) : z.trace.re = (star z).trace.re := by
      rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
      rfl
    exact (h (y*star x)).trans (by rw [star_mul, star_star])
  add_left x y z := by simp [add_mul]
  smul_left x y z := by simp

attribute [local instance] frobInner

variable (G : Gauge)

abbrev lieDim := Module.finrank ℝ G.Alg
abbrev ColorIndex := Fin G.lieDim
abbrev Color := EuclideanSpace ℝ G.ColorIndex

/-- scale factor from physical to Frobenius coordinates. -/
def colorScale := Real.sqrt G.repDim

theorem colorScale_pos : 0 < G.colorScale := Real.sqrt_pos.2 (by exact_mod_cast G.dimPos)
theorem colorScale_sq : G.colorScale^2 = (G.repDim : ℝ) := Real.sq_sqrt (by positivity)

/-- A fixed orthogonal frame with the physical normalization. -/
def colorIso : G.Color ≃ₗ[ℝ] G.Alg :=
  (stdOrthonormalBasis ℝ G.Alg).repr.symm.toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ G.Alg G.colorScale G.colorScale_pos.ne')

theorem inner_frob_color (c d : G.Color) :
    inner ℝ (G.colorIso c) (G.colorIso d) = (G.repDim : ℝ) * inner ℝ c d := by
  let a := (stdOrthonormalBasis ℝ G.Alg).repr
  change inner ℝ (G.colorScale • (a.symm c)) (G.colorScale • a.symm d) = _
  rw [real_inner_smul_left (a.symm c) _ G.colorScale,
    real_inner_smul_right (a.symm c) (a.symm d) G.colorScale, a.symm.inner_map_map, ← mul_assoc,
    ← sq, G.colorScale_sq]

def colorMat : G.Color →ₗ[ℝ] G.Mat := G.lie.subtype.comp G.colorIso.toLinearMap

theorem colorMat_mem (c : G.Color) : G.colorMat c ∈ G.lie := (G.colorIso c).property

theorem colorMat_skew (c : G.Color) : star (G.colorMat c) = -(G.colorMat c) :=
  G.generates_skew (G.colorMat_mem c)

theorem trace_color (c d : G.Color) :
    -(G.colorMat c * G.colorMat d).trace.re = (G.repDim : ℝ) * inner ℝ c d := by
  have hc := G.inner_frob_color c d
  change (G.colorMat c * star (G.colorMat d)).trace.re = _ at hc
  simpa only [G.colorMat_skew d, mul_neg, Matrix.trace_neg, Complex.neg_re] using hc

theorem trace_color_real (c d : G.Color) : (G.colorMat c * G.colorMat d).trace.im = 0 := by
  let A := G.colorMat c
  let B := G.colorMat d
  have e : star ((A*B).trace) = (A*B).trace := by
    rw [← Matrix.trace_conjTranspose, ← Matrix.star_eq_conjTranspose, star_mul]
    rw [show star A = -A from G.colorMat_skew c, show star B = -B from G.colorMat_skew d,
      neg_mul_neg, Matrix.trace_mul_comm]
  have h : -(A*B).trace.im = (A*B).trace.im := congr_arg Complex.im e
  change (A*B).trace.im = 0
  linarith

theorem colorMat_injective : Function.Injective G.colorMat :=
  Subtype.val_injective.comp G.colorIso.injective

theorem colorMat_norm (c : G.Color) : ‖G.colorMat c‖ = G.colorScale * ‖c‖ := by
  let a := (stdOrthonormalBasis ℝ G.Alg).repr
  change ‖G.colorScale • (a.symm c)‖ = _
  rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg G.colorScale_pos.le]

def projectColor : G.Mat →ₗ[ℝ] G.Color :=
  G.colorIso.symm.toLinearMap.comp G.lie.orthogonalProjectionOnto.toLinearMap

theorem colorMat_project (A : G.Mat) : G.colorMat (G.projectColor A) = G.lie.starProjection A := by
  change (G.colorIso (G.colorIso.symm (G.lie.orthogonalProjectionOnto A)) : G.Alg).val = _
  rw [LinearEquiv.apply_symm_apply]; rfl

@[simp] theorem colorMat_project_self {A : G.Mat} (h : A ∈ G.lie) :
    G.colorMat (G.projectColor A) = A := by rw [colorMat_project]; exact Submodule.starProjection_eq_self_iff.mpr h

@[simp] theorem project_colorMat (c : G.Color) : G.projectColor (G.colorMat c) = c :=
  G.colorMat_injective (G.colorMat_project_self (G.colorMat_mem _))

theorem project_norm (A : G.Mat) : ‖G.projectColor A‖ ≤ ‖A‖ / G.colorScale := by
  rw [le_div_iff₀ G.colorScale_pos, mul_comm, ← colorMat_norm, colorMat_project]
  exact G.lie.norm_starProjection_apply_le A

/-- Gauge group adjoint through coordinates -/
def adjoint (u : G.El) : G.Color →ₗ[ℝ] G.Color where
  toFun c := G.projectColor (G.conjugate u (G.colorMat c))
  map_add' := by intros; simp [conjugate, mul_add, add_mul]
  map_smul' := by intros; simp [conjugate]

@[simp] theorem mat_adjoint (u : G.El) (c : G.Color) :
    G.colorMat (G.adjoint u c) = G.conjugate u (G.colorMat c) :=
  G.colorMat_project_self (G.conjugate_mem _ (G.colorMat_mem c))

@[simp] theorem adjoint_one (c : G.Color) : G.adjoint 1 c = c := by
  apply G.colorMat_injective; simp [conjugate]

theorem adjoint_mul (u v : G.El) (c : G.Color) :
    G.adjoint (u*v) c = G.adjoint u (G.adjoint v c) := by
  apply G.colorMat_injective; simp [conjugate, mul_assoc]

@[simp] theorem norm_adjoint (u : G.El) (c : G.Color) : ‖G.adjoint u c‖ = ‖c‖ := by
  apply mul_left_cancel₀ G.colorScale_pos.ne'
  rw [← G.colorMat_norm, G.mat_adjoint, conjugate, frob_mul_eq, mul_frob_eq, colorMat_norm]
  · exact G.mat_star_mul u
  · simp

def ad : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] G.Color where
  toFun c := {
    toFun d := G.projectColor (G.colorMat c * G.colorMat d - G.colorMat d * G.colorMat c)
    map_add' d e := by simp [mul_add, add_mul]; abel
    map_smul' t d := by simp [smul_sub] }
  map_add' c d := by
    apply LinearMap.ext
    intro f
    dsimp
    simp [mul_add, add_mul]; abel
  map_smul' t c := by
    apply LinearMap.ext
    intro f
    dsimp
    simp [smul_sub]

@[simp] theorem colorMat_ad (c d : G.Color) :
    G.colorMat (G.ad c d) = G.colorMat c * G.colorMat d - G.colorMat d * G.colorMat c :=
  G.colorMat_project_self (G.bracket_mem (G.colorMat_mem _) (G.colorMat_mem _))

theorem lieExp_mem (c : G.Color) : exp (G.colorMat c) ∈ range G.mat := by
  simpa only [one_smul] using (mem_lie G).mp (G.colorMat_mem c) 1

/-- Actual exponential into the gauge group. -/
def lieExp (c : G.Color) : G.El := (G.lieExp_mem c).choose

@[simp] theorem mat_lieExp (c : G.Color) : G.mat (G.lieExp c) = exp (G.colorMat c) :=
  (G.lieExp_mem c).choose_spec

@[fun_prop] theorem lieExp_cont : Continuous G.lieExp := by
  have h := G.continuous_mat.isClosedEmbedding G.mat_injective
  rw [h.isEmbedding.continuous_iff]
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  simp only [Function.comp_def, G.mat_lieExp]
  exact exp_continuous.comp G.colorMat.continuous_of_finiteDimensional

/-- projection of the real skew part, in physical coordinates. -/
def curvature (u : G.El) := G.projectColor ((1/2 : ℝ) • (G.mat u - G.mat u⁻¹))

@[simp] theorem curvature_inv (u : G.El) : G.curvature u⁻¹ = - G.curvature u := by
  unfold curvature
  rw [inv_inv, ← neg_sub, smul_neg, map_neg]

/-- `C_A`, fixed in terms of the trace of the adjoint action on physical colors. -/
def casimir : ℝ :=
  let b := EuclideanSpace.basisFun G.ColorIndex ℝ;
  -(∑ i : G.ColorIndex, LinearMap.trace ℝ G.Color (G.ad (b i) ∘ₗ G.ad (b i))) / G.lieDim

def slopeConstant : ℝ := 11 * G.casimir / (24 * Real.pi ^ 2)

end YM.Gauge
