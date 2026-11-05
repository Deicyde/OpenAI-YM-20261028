import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Group.Tannery
import YM.Analysis.Polydisc
import YM.PREC.Implicit
import YM.Pressure.Seeds

/-!
# Color rigidity of the loop scalar and its jets

Simple nonabelian matrix algebra, NOT necessarily connected gauge group.
Includes the nonsymmetric bilinear case for opposite oriented coefficient legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Set Filter MeasureTheory NormedSpace Precision LinearMap
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators ENNReal InnerProductSpace
variable {G : Gauge}

lemma adjoint_rate (a b : G.Color) :
    HasDerivAt (fun t : ℝ => G.adjoint (G.lieExp (t • a)) b) (G.ad a b) 0 := by
  have he : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • a))) (G.colorMat a) 0 :=
    (side _ G.expDiff_zero.differentiableAt a).congr_deriv (DFunLike.congr_fun G.expDiff_zero.fderiv a)
  have hf := (he.mul_const (G.colorMat b)).mul he.star
  simp only [zero_smul, G.mat_lieExp_zero, G.mat_one, one_mul, star_one, mul_one, G.colorMat_skew,
    mul_neg, ← sub_eq_add_neg] at hf
  exact G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (l:=G.projectColor) (0:ℝ) hf

lemma ad_flip (a b : G.Color) : G.ad a b = -G.ad b a := by
  apply G.colorMat_injective
  rw [map_neg,G.colorMat_ad,G.colorMat_ad, neg_sub]

lemma no_functional {V : Type*} [AddCommGroup V] [Module ℝ V] (h : G.Simple)
    (L : G.Color →ₗ[ℝ] V) (hi : ∀ x y, L (G.ad x y)=0) : L = 0 := by
  rcases h.ideals L.ker (fun x y _ => hi x y) with hbot|htop
  · obtain ⟨x,y,he⟩ := h.nonabelian
    exact False.elim (he ((L.ker.eq_bot_iff.mp hbot) _ (hi x y)))
  exact LinearMap.ker_eq_top.mp htop

lemma invariant_null {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : G.Simple)
    (L : G.Color →ₗ[ℝ] V) (hi : ∀ u x, L (G.adjoint u x) = L x) : L = 0 := by
  refine no_functional h _ (fun x y => ?_)
  have hr := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (l:=L) 0 (adjoint_rate x y)
  simp only [Function.comp_def, hi] at hr
  exact hr.unique (hasDerivAt_const (0:ℝ) (L y))



private lemma orth_invariant (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (h : ∀ u x y, B (G.adjoint u x) (G.adjoint u y) = B x y) (x y z : G.Color) :
    B (G.ad x y) z = -B y (G.ad x z) := by
  let L := (LinearMap.toContinuousLinearMap.toLinearMap.comp B).toContinuousLinearMap
  have he := (L.hasFDerivAt.comp_hasDerivAt 0 (adjoint_rate x y)).clm_apply (adjoint_rate x z)
  change HasDerivAt (fun t : ℝ => B (G.adjoint (G.lieExp (t • x)) y) (G.adjoint (G.lieExp (t • x)) z))
    (_ + _) 0 at he
  simp_rw [h] at he
  have ht := he.unique (hasDerivAt_const (0:ℝ) (B y z))
  change B (G.ad x y) (G.adjoint _ z) + B (G.adjoint _ y) (G.ad x z) = 0 at ht
  simp only [zero_smul,G.mat_lieExp_zero,G.adjoint_one] at ht
  exact eq_neg_of_add_eq_zero_left ht

private lemma antisymmetric_null (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = -B y x)
    (hi : ∀ x y z, B (G.ad x y) z = - B y (G.ad x z)) (x y : G.Color) : B x y = 0 := by
  have he (x y z : G.Color) : B (G.ad x y) z = -B (G.ad z x) y := by
    rw [hi, ad_flip x z, map_neg, neg_neg, hs y]
  have ht (x y z : G.Color) : B (G.ad x y) z = 0 := by linarith [he x y z, he z x y, he y z x]
  rw [no_functional h B (fun x y => LinearMap.ext (fun z => ht x y z))]; simp

lemma scalar_form (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (hi : ∀ u x y, B (G.adjoint u x) (G.adjoint u y) = B x y) :
    ∃ a : ℝ, ∀ x y, B x y = a * ⟪x,y⟫_ℝ := by
  have hk := orth_invariant B hi
  apply Gauge.invariant_scalar h _ _ hk
  let C := B - B.flip
  have ha (x y) : C x y = - C y x := by simp [C]
  have hb (x y z : G.Color) : C (G.ad x y) z = - C y (G.ad x z) := by
    simp only [C, LinearMap.sub_apply, LinearMap.flip_apply, neg_sub]
    rw [hk x y z,hk x z y]; abel
  exact fun x y => sub_eq_zero.mp (antisymmetric_null h C ha hb x y)

lemma scalar_complex (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℂ)
    (hi : ∀ u x y, B (G.adjoint u x) (G.adjoint u y) = B x y) :
    ∃ a : ℂ, ∀ x y, B x y = a * ↑⟪x,y⟫_ℝ := by
  have split (L : ℂ →ₗ[ℝ] ℝ) : ∃ a : ℝ, ∀ x y, L (B x y) = a * ⟪x,y⟫_ℝ :=
    scalar_form h (B.compr₂ L) (fun u x y => congr_arg L (hi u x y))
  obtain ⟨a,ha⟩ := split Complex.reLm
  obtain ⟨b,hb⟩ := split Complex.imLm
  exact ⟨⟨a,b⟩,fun x y => Complex.ext (by simpa using ha x y) (by simpa using hb x y)⟩
end YM.Push.Loops
