import YM.Euclid.Comparator
import YM.Euclid.Words
import YM.Gauge.Casimir
import YM.Gauge.Chart
import YM.Next.MAXWELL.Kernel



/-! # Low invariant tensors for any actual nonabelian Simple Gauge -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Analysis MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge}

def irreduc (B : G.Color → ℝ) := ∀ u : G.El, ∀ x, B (G.adjoint u x)=B x

def irreduc₂ (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ) := ∀ u : G.El, ∀ x y, B (G.adjoint u x) (G.adjoint u y)=B x y

lemma adj_cont (x : G.Color) : Continuous fun u => G.adjoint u x := by
  let J := fun u : G.El => G.mat u * G.colorMat x * star (G.mat u)
  have hp : Continuous J := (G.continuous_mat.mul continuous_const).mul G.continuous_mat.star
  exact G.projectColor.continuous_of_finiteDimensional.comp hp

lemma adj_has (x y : G.Color) : HasDerivAt (fun s : ℝ => G.adjoint (G.lieExp (s • x)) y) (G.ad x y) 0 := by
  let L := fun s : ℝ => G.mat (G.lieExp (s • x))
  have he : L 0=1 := by simp [L]
  have hp : HasDerivAt L (G.colorMat x) 0 := by
    unfold L; simp only [Gauge.mat_lieExp, map_smul]
    simpa using! hasDerivAt_exp_smul_const (G.colorMat x) (0:ℝ)
  have ht := (hp.mul_const (G.colorMat y)).mul hp.star
  change HasDerivAt (fun s => L s*G.colorMat y*star (L s))
    (G.colorMat x * G.colorMat y * star (L 0) + (L 0 * G.colorMat y) * star (G.colorMat x)) 0 at ht
  rw [he,star_one,mul_one, one_mul,G.colorMat_skew, mul_neg, ← sub_eq_add_neg] at ht
  exact G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) ht

lemma skew_ad (x y : G.Color) : G.ad x y = -G.ad y x := by
  apply G.colorMat_injective
  rw [map_neg,G.colorMat_ad,G.colorMat_ad,neg_sub]

lemma ad_span (h : G.Simple) : Submodule.span ℝ {x|∃ a b, G.ad a b=x}=⊤ := by
  let V := Submodule.span ℝ {x|∃ a b,G.ad a b=x}
  have ht (a b) : G.ad a b ∈ V := Submodule.subset_span ⟨_,_,rfl⟩
  apply (h.ideals V fun a b _ => ht a b).resolve_left; intro hv
  obtain ⟨x,y,hxy⟩ := h.nonabelian
  exact hxy ((Submodule.mem_bot ..).mp (hv ▸ ht x y))

lemma singles_inv (h : G.Simple) (v : G.Color →ₗ[ℝ] ℝ) (H : irreduc (G:=G) v) : v=0 := by
  let L := v.toContinuousLinearMap
  refine LinearMap.ext_on (ad_span h) ?_
  rintro x ⟨a,b,rfl⟩
  have ht := L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (adj_has a b)
  change HasDerivAt (fun s : ℝ => v (G.adjoint (G.lieExp (s • a)) b)) (v (G.ad a b)) 0 at ht
  simp_rw [H (G.lieExp _) _] at ht; exact ht.unique (hasDerivAt_const ..)

lemma invariant_two (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ) (H : irreduc₂ B) :
    ∃ c : ℝ, ∀ x y, B x y=c * ⟪x,y⟫_ℝ := by
  let f := LinearMap.toContinuousLinearMap.toLinearMap.comp B
  let L := f.toContinuousLinearMap
  have he (x y z) : B (G.ad x y) z = -B y (G.ad x z) := by
    let K (b : G.Color) := fun t : ℝ => G.adjoint (G.lieExp (t • x)) b
    have hk (b) : K b 0=b := by simp [K]
    have hh := ((L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (show HasDerivAt (K y) _ 0 from adj_has x y)).clm_apply
      (show HasDerivAt (K z) _ 0 from adj_has x z))
    simp only [Function.comp_apply,hk] at hh
    have ht (t : ℝ) : L (K y t) (K z t)=B y z := H _ _ _
    simp_rw [ht] at hh
    have hr := hh.unique (hasDerivAt_const ..)
    exact eq_neg_of_add_eq_zero_left hr
  apply Gauge.invariant_scalar h B _ he
  have hc (x y z) : B (G.ad x y) z=B x (G.ad y z) := by rw [skew_ad x y,map_neg,LinearMap.neg_apply,he,neg_neg]
  have hv (x y z) : B (G.ad x y) z=B z (G.ad x y) := by rw [he,skew_ad x z, map_neg,neg_neg,← hc, he, skew_ad, map_neg,neg_neg]
  intro x y
  have heq : B.flip y=B y := LinearMap.ext_on (ad_span h) (by rintro z ⟨a,b,rfl⟩; exact hv a b y)
  exact LinearMap.congr_fun heq x
end YM.Maxwell.Free
