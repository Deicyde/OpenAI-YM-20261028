import YM.Gauge.Colors
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The adjoint Casimir constant of the gauge image

in the color coordinates fixed in `Colors`.
In particular the simplicity here is *real*, and has actual consequences for
later Ward and schedule arguments.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Gauge

open LinearMap Submodule
open scoped Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge}

theorem Simple.nonabelian (h : G.Simple) : ∃ x y, G.ad x y ≠ 0 := by
  obtain ⟨X, hX, Y, hY, hN⟩ := h.1
  refine ⟨G.projectColor X, G.projectColor Y, fun h0 ↦ ?_⟩
  apply hN
  have ht := congr_arg (fun a : G.Color => G.colorMat a) h0
  simpa only [G.colorMat_ad, G.colorMat_project_self hX, G.colorMat_project_self hY, map_zero]
    using ht

theorem Simple.ideals (h : G.Simple) (I : Submodule ℝ G.Color)
    (H : ∀ x y, y ∈ I → G.ad x y ∈ I) : I = ⊥ ∨ I = ⊤ := by
  have hle : I.map G.colorMat ≤ G.lie := by
    rintro a ⟨c, -, rfl⟩
    exact G.colorMat_mem c
  have hb : ∀ x ∈ G.lie, ∀ y ∈ I.map G.colorMat, x*y-y*x ∈ I.map G.colorMat := by
    rintro X hX y ⟨c, hc, rfl⟩
    exact ⟨G.ad (G.projectColor X) c, H _ c hc, by rw [colorMat_ad, G.colorMat_project_self hX]⟩
  rcases h.2 _ hle hb with hbot | htop
  · left
    refine le_antisymm (fun c hc ↦ ?_) bot_le
    rw [mem_bot]
    apply G.colorMat_injective
    rw [map_zero]
    rw [← Submodule.mem_bot ℝ]
    rw [← hbot]
    exact Submodule.mem_map_of_mem hc
  · right
    refine le_antisymm le_top (fun c _ ↦ ?_)
    obtain ⟨d, hd, hh⟩ : G.colorMat c ∈ I.map G.colorMat := htop.symm ▸ G.colorMat_mem c
    rwa [← G.colorMat_injective hh]

theorem Simple.nontrivial_color (h : G.Simple) : Nontrivial G.Color := by
  obtain ⟨x, y, H⟩ := h.nonabelian
  exact ⟨x, 0, fun he ↦ H (by rw [he]; simp)⟩

theorem ad_jacobi (x y : G.Color) :
    G.ad (G.ad x y) = G.ad x * G.ad y - G.ad y * G.ad x := by
  apply LinearMap.ext
  intro z
  apply G.colorMat_injective
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, colorMat_ad]
  noncomm_ring

theorem ad_skew (x y z : G.Color) : ⟪G.ad x y, z⟫_ℝ = -⟪y, G.ad x z⟫_ℝ := by
  apply mul_left_cancel₀ (show (G.repDim : ℝ) ≠ 0 from ne_of_gt (by exact_mod_cast G.dimPos))
  rw [← trace_color, mul_neg, ← trace_color, colorMat_ad, colorMat_ad]
  simp only [sub_mul, mul_sub, Matrix.trace_sub, Complex.sub_re, neg_sub]
  rw [Matrix.mul_assoc, Matrix.trace_mul_cycle']
  rw [Matrix.trace_mul_comm]
  rw [mul_assoc (G.colorMat x), Matrix.trace_mul_comm (G.colorMat x), mul_assoc (G.colorMat y), mul_assoc (G.colorMat y)]

def minusKilling (G : Gauge) : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ where
  toFun x := {
    toFun y := - trace ℝ G.Color (G.ad x * G.ad y)
    map_add' y z := by rw [map_add, mul_add, map_add, neg_add]
    map_smul' := by intros; simp }
  map_add' x y := by
    apply LinearMap.ext
    intro f
    dsimp
    rw [map_add, add_mul, map_add, neg_add]
  map_smul' t x := by
    apply LinearMap.ext
    intro f
    dsimp
    simp

theorem minusKilling_symm (x y : G.Color) : G.minusKilling x y = G.minusKilling y x := by
  simp only [minusKilling, LinearMap.coe_mk, AddHom.coe_mk, trace_mul_comm _ (G.ad x)]

theorem minusKilling_invariant (x y z : G.Color) :
    G.minusKilling (G.ad x y) z = - G.minusKilling y (G.ad x z) := by
  simp only [minusKilling, LinearMap.coe_mk, AddHom.coe_mk, ad_jacobi, sub_mul, mul_sub, map_sub,
    neg_sub]
  simp only [mul_assoc]
  rw [trace_mul_comm _ (G.ad x), mul_assoc]

/-- Every real symmetric Lie-invariant form has this shape. -/
theorem invariant_scalar (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x)
    (hi : ∀ x y z, B (G.ad x y) z = - B y (G.ad x z)) :
    ∃ c : ℝ, ∀ x y : G.Color, B x y = c * ⟪x, y⟫_ℝ := by
  letI := h.nontrivial_color
  let A : Module.End ℝ G.Color :=
    ((InnerProductSpace.toDual ℝ G.Color).symm.toLinearEquiv.toLinearMap :
      (G.Color →L[ℝ] ℝ) →ₗ[ℝ] G.Color).comp (toContinuousLinearMap.toLinearMap.comp B)
  have hA (x y) : ⟪A x, y⟫_ℝ = B x y :=
    InnerProductSpace.toDual_symm_apply
  have ha : A.IsSymmetric := fun x y ↦ by rw [hA, real_inner_comm (A y), hA, hs]
  let n := Module.finrank ℝ G.Color
  let i : Fin n := ⟨0, Module.finrank_pos⟩
  let c : ℝ := ha.eigenvalues (rfl : Module.finrank ℝ G.Color = n) i
  have hall (x y : G.Color) : A (G.ad x y) = G.ad x (A y) := by
    apply ext_inner_right ℝ
    intro z
    rw [hA, hi, ad_skew, hA]
  have he : Module.End.eigenspace A c = ⊤ := by
    apply Or.resolve_left (h.ideals _ ?_)
    · exact Module.End.hasEigenvalue_of_hasEigenvector (ha.hasEigenvector_eigenvectorBasis rfl i)
    intro x y hy
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    rw [hall, hy, map_smul]
  refine ⟨c, fun x y ↦ ?_⟩
  rw [← hA, Module.End.mem_eigenspace_iff.mp (show x ∈ Module.End.eigenspace A c by simp [he]),
    real_inner_smul_left]

/-- `-tr ad_X²` is actually a Frobenius norm square on color endomorphisms. -/
theorem minusKilling_sq (x : G.Color) (b : OrthonormalBasis G.ColorIndex ℝ G.Color) :
    G.minusKilling x x = ∑ i, ‖G.ad x (b i)‖ ^ 2 := by
  simp only [minusKilling, LinearMap.coe_mk, AddHom.coe_mk]
  rw [trace_eq_matrix_trace ℝ b.toBasis, Matrix.trace, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply, toMatrix_apply, b.coe_toBasis_repr_apply,
    Module.End.mul_apply, b.repr_apply_apply, b.coe_toBasis]
  rw [← ad_skew]
  exact real_inner_self_eq_norm_sq _


theorem trace_adjoint (h : G.Simple) (x y : G.Color) :
    -trace ℝ G.Color (G.ad x * G.ad y) = G.casimir * ⟪x, y⟫_ℝ := by
  obtain ⟨c, hc⟩ := invariant_scalar h G.minusKilling minusKilling_symm minusKilling_invariant
  haveI := h.nontrivial_color
  let b := EuclideanSpace.basisFun G.ColorIndex ℝ
  have hs (i) : trace ℝ G.Color (G.ad (b i) ∘ₗ G.ad (b i)) = - c := by
    rw [← neg_eq_iff_eq_neg]
    change G.minusKilling (b i) (b i) = _
    rw [hc, b.inner_eq_one, mul_one]
  have hn : G.lieDim ≠ 0 := by
    rw [lieDim, ← G.colorIso.finrank_eq]
    exact Module.finrank_pos.ne'
  have e : G.casimir = c := by
    change -(∑ i, trace ℝ G.Color (G.ad (b i) ∘ₗ G.ad (b i))) / G.lieDim = _
    simp only [hs, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    simp [hn]
  rw [e]
  exact hc x y

theorem casimir_pos (h : G.Simple) : 0 < G.casimir := by
  obtain ⟨x, y, he⟩ := h.nonabelian
  let b := EuclideanSpace.basisFun G.ColorIndex ℝ
  obtain ⟨i, hi⟩ : ∃ i, G.ad x (b i) ≠ 0 := by
    by_contra! hn
    have ht : G.ad x = 0 := b.toBasis.ext fun i ↦ hn i
    simp [ht] at he
  have hk : 0 < G.minusKilling x x := by
    rw [minusKilling_sq x b]
    exact Finset.sum_pos' (fun _ _ ↦ sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi)⟩
  change 0 < - trace ℝ G.Color (G.ad x * G.ad x) at hk
  rw [trace_adjoint h] at hk
  exact pos_of_mul_pos_left hk (real_inner_self_nonneg)

theorem slopeConstant_pos (h : G.Simple) : 0 < G.slopeConstant := by
  have := casimir_pos h
  unfold slopeConstant; positivity

end YM.Gauge
