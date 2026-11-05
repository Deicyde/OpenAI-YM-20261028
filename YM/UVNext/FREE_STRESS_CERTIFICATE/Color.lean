import YM.Gauge.Casimir

/-!
# Invariants of the actual color action used by the free low-weight calculation

In particular we need not just *symmetric* real invariant forms. No connectedness
assumption. Differentiate on the actual image exponential curves. Normalization
of `Color` and its inner product is exactly that of `Gauge.Colors`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress

open Function Set Filter LinearMap NormedSpace
open scoped Matrix.Norms.Frobenius RealInnerProductSpace
variable {G : Gauge}

theorem adjoint_derivative (x y : G.Color) :
    HasDerivAt (fun t : ℝ => G.adjoint (G.lieExp (t • x)) y) (G.ad x y) 0 := by
  let a := fun t : ℝ => exp (t • G.colorMat x)
  have he : HasDerivAt a (G.colorMat x) 0 := by
    simpa [a] using! hasDerivAt_exp_smul_const (G.colorMat x) (0 : ℝ)
  have h := (he.mul_const (G.colorMat y)).mul he.star
  have hd : HasDerivAt (fun t => a t * G.colorMat y * star (a t))
      (G.colorMat x * G.colorMat y - G.colorMat y * G.colorMat x) 0 := by
    simpa [a, G.colorMat_skew, sub_eq_add_neg] using! h
  let P := G.projectColor.toContinuousLinearMap
  have H := P.hasFDerivAt.comp_hasDerivAt (0:ℝ) hd
  change HasDerivAt (fun t : ℝ => G.projectColor (G.conjugate (G.lieExp (t • x)) (G.colorMat y))) _ _
  unfold Gauge.conjugate
  simp_rw [G.mat_lieExp,G.colorMat.map_smul]
  exact H

theorem ad_swap (x y : G.Color) : G.ad y x = -G.ad x y := by
  apply G.colorMat_injective
  rw [G.colorMat_ad, map_neg, G.colorMat_ad, neg_sub]

def brackets (G : Gauge) := Submodule.span ℝ {w : G.Color | ∃ x y : G.Color, G.ad x y = w}

theorem generates_color (h : G.Simple) : brackets G = ⊤ := by
  have hw (x y) : G.ad x y ∈ brackets G := Submodule.subset_span ⟨x,y,rfl⟩
  apply Or.resolve_left (h.ideals _ (fun x y _ => hw x y))
  obtain ⟨x,y,hne⟩ := h.nonabelian
  intro he
  apply hne
  exact Submodule.mem_bot ℝ |>.mp (he ▸ hw x y)

theorem no_linear {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (h : G.Simple) (f : G.Color →ₗ[ℝ] Y) (hi : ∀ u v, f (G.adjoint u v) = f v) : f=0 := by
  apply LinearMap.ext_on (s:={w : G.Color | ∃ x y, G.ad x y = w}) (generates_color h)
  rintro _ ⟨x,y,rfl⟩
  let F := f.toContinuousLinearMap
  have H := F.hasFDerivAt.comp_hasDerivAt (0:ℝ) (adjoint_derivative x y)
  change HasDerivAt (F ∘ (fun t : ℝ => G.adjoint (G.lieExp (t • x)) y)) _ _ at H
  rw [show (F ∘ (fun t : ℝ => G.adjoint (G.lieExp (t • x)) y)) = fun _ => f y from funext fun _ => hi _ _] at H
  exact H.unique (hasDerivAt_const _ _)

theorem bilinear_lie (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (hi : ∀ u x y, B (G.adjoint u x) (G.adjoint u y) = B x y)
    (x y z : G.Color) : B (G.ad x y) z = - B y (G.ad x z) := by
  let F := LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp B)
  have H := (F.hasFDerivAt.comp_hasDerivAt (0:ℝ) (adjoint_derivative x y)).clm_apply (adjoint_derivative x z)
  rw [show (fun t : ℝ => (F ∘ fun t : ℝ => G.adjoint (G.lieExp (t • x)) y) t
      ((fun t : ℝ => G.adjoint (G.lieExp (t • x)) z) t)) = fun _ => B y z from funext fun _ => hi _ _ _] at H
  have h := H.unique (hasDerivAt_const _ _)
  have he : G.lieExp 0 = 1 := G.mat_injective (by simp)
  simp only [Function.comp_apply, zero_smul, he, G.adjoint_one] at h
  exact eq_neg_of_add_eq_zero_left (show B _ z + B y _ = 0 from h)

-- A Lie-invariant alternating form vanishes on brackets (the cyclic shifts
-- of A([x,y],z) each negate it).
private theorem alternating (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (hi : ∀ x y z, B (G.ad x y) z = - B y (G.ad x z))
    (ha : ∀ x y, B x y = -B y x) : B=0 := by
  have hc (x y z) : B (G.ad x y) z = - B (G.ad z x) y := by
    rw [hi, ha y, neg_neg, ad_swap, map_neg, LinearMap.neg_apply]
  apply LinearMap.ext_on (s:={w : G.Color | ∃ x y, G.ad x y = w}) (generates_color h)
  rintro _ ⟨x,y,rfl⟩
  ext z
  have h1 := hc x y z; have h2 := hc z x y; have h3 := hc y z x
  change B _ _ = 0; linarith

theorem real_color_form (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (hi : ∀ u x y, B (G.adjoint u x) (G.adjoint u y) = B x y) :
    ∃ c : ℝ, ∀ x y, B x y = c * inner ℝ x y := by
  have hl : ∀ x y z, _ := bilinear_lie B hi
  have he : B-B.flip=0 := alternating h _ (fun x y z => by
    simp only [LinearMap.sub_apply, flip_apply, hl x y z, ← neg_eq_iff_eq_neg.mpr (hl x z y)]; abel)
    (by intro x y; simp)
  apply Gauge.invariant_scalar h B (fun x y => ?_) hl
  exact LinearMap.congr_fun (LinearMap.congr_fun (show B = B.flip from sub_eq_zero.mp he) x) y

theorem complex_color_form (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℂ)
    (hi : ∀ u x y, B (G.adjoint u x) (G.adjoint u y) = B x y) :
    ∃ c : ℂ, ∀ x y, B x y = (inner ℝ x y : ℝ) • c := by
  have H (f : ℂ →ₗ[ℝ] ℝ) : ∃ c : ℝ, ∀ x y, f (B x y) = c * inner ℝ x y :=
    real_color_form h ((LinearMap.llcomp ℝ _ ℂ ℝ f).comp B) (fun u x y => congr_arg f (hi u x y))
  obtain ⟨r,hr⟩ := H Complex.reLm; obtain ⟨s,hs⟩ := H Complex.imLm
  refine ⟨⟨r,s⟩,fun x y => ?_⟩
  apply Complex.ext
  · rw [show (B x y).re = _ from hr x y]
    simp [mul_comm]
  · rw [show (B x y).im = _ from hs x y]
    simp [mul_comm]

end YM.UVNext.FreeStress
