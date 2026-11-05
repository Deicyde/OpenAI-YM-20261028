import YM.Next.EXTRACTION.Tails

/-!
# Invariants in low slot degree

Work with the actual real Lie algebra in physical color coordinates. Simplicity of
that algebra is important: adjoint-invariant linear forms vanish; *any* invariant bilinear
form (even potentially across different Taylor degrees or antisymmetric index types) is a
multiple of the inner product. No dimension-at-infinity/color group assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Function Filter Set Gauge LinearMap
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge}

theorem inner_adjoint (g : G.El) (x y : G.Color) : ⟪G.adjoint g x,G.adjoint g y⟫_ℝ = ⟪x,y⟫_ℝ :=
  (LinearIsometry.inner_map_map (⟨G.adjoint g, G.norm_adjoint g⟩ : G.Color →ₗᵢ[ℝ] G.Color)) x y

theorem color_change (x y : G.Color) : HasDerivAt (fun t : ℝ => G.adjoint (G.lieExp (t • x)) y)
    (G.ad x y) 0 := by
  let U := fun t : ℝ => G.mat (G.lieExp (t • x))
  have hx : HasDerivAt U (G.colorMat x) 0 := by
    unfold U; simp only [G.mat_lieExp, map_smul]
    simpa using! hasDerivAt_exp_smul_const (G.colorMat x) (0 : ℝ)
  have he := G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    ((hx.mul_const (G.colorMat y)).mul hx.star)
  refine he.congr_deriv ?_
  simp only [U, zero_smul, G.mat_lieExp, map_zero, NormedSpace.exp_zero, star_one,
    G.colorMat_skew, mul_one, one_mul, mul_neg]
  rfl

theorem ad_antisym (x y : G.Color) : G.ad x y = - G.ad y x := by
  apply G.colorMat_injective; simp only [map_neg, G.colorMat_ad,neg_sub]

section Linear
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem linear_zero (H : G.Simple) (l : G.Color →ₗ[ℝ] V) (hl : ∀ x y, l (G.ad x y) = 0) : l = 0 := by
  obtain h|h := H.ideals (LinearMap.ker l) (fun x y _ => hl x y)
  · obtain ⟨x,y,hz⟩ := H.nonabelian
    exact (hz ((LinearMap.ker_eq_bot.mp h) ((hl x y).trans (map_zero l).symm))).elim
  exact LinearMap.ker_eq_top.mp h

theorem linear_invariant (H : G.Simple) (l : G.Color →ₗ[ℝ] V)
    (h : ∀ g x, l (G.adjoint g x) = l x) : l = 0 := by
  refine linear_zero H l fun x y => ?_
  have he : HasDerivAt (fun t : ℝ => l (G.adjoint (G.lieExp (t • x)) y)) (l (G.ad x y)) 0 :=
    l.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (color_change x y)
  simp_rw [h] at he
  exact he.unique (hasDerivAt_const ..)

lemma bilinear_infinitesimal (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] V)
    (hb : ∀ g x y, B (G.adjoint g x) (G.adjoint g y) = B x y) (x y z : G.Color) :
    B (G.ad x y) z = - B y (G.ad x z) := by
  let L := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B)
  have he := (L.hasFDerivAt.comp_hasDerivAt 0 (color_change x y)).clm_apply (color_change x z)
  have hw (v : G.Color) : G.adjoint (G.lieExp ((0:ℝ) • x)) v = v := by simp
  change HasDerivAt (fun t => B (G.adjoint (G.lieExp (t • x)) y) (G.adjoint (G.lieExp (t • x)) z))
    (B (G.ad x y) _ + B _ (G.ad x z)) 0 at he
  simp_rw [hw, hb] at he
  exact eq_neg_of_add_eq_zero_left (he.unique (hasDerivAt_const ..))
end Linear

lemma bilinear_real (H : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (hi : ∀ x y z, B (G.ad x y) z = - B y (G.ad x z)) : ∃ c : ℝ, ∀ x y, B x y = c * ⟪x,y⟫_ℝ := by
  let A := B - B.flip
  have hS (x y : G.Color) : A x y = - A y x := by dsimp [A]; ring
  have hI (x y z : G.Color) : A (G.ad x y) z = A (G.ad x z) y := by dsimp [A]; rw [hi,hi x z]; ring
  have hW (x y z : G.Color) : A (G.ad x y) z = - A (G.ad y x) z := by nth_rw 1 [ad_antisym]; simp
  have he (x y z : G.Color) : A (G.ad x y) z = 0 := by linarith [hI x y z,hW x z y,hI z x y,hW z y x,hI y z x,hW y x z]
  apply invariant_scalar H B (fun x y => sub_eq_zero.mp ?_) hi
  exact LinearMap.congr_fun (linear_zero H (A.flip y) (fun _ _ => he _ _ _)) x

/-- Scale is specified, not just existence. -/
theorem bilinear_invariant (H : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℂ)
    (h : ∀ g x y, B (G.adjoint g x) (G.adjoint g y) = B x y) {e : G.Color} (he : ‖e‖ = 1) (x y : G.Color) :
    B x y = ⟪x,y⟫_ℝ • B e e := by
  have hs (l : ℂ →ₗ[ℝ] ℝ) : l (B x y) = ⟪x,y⟫_ℝ * l (B e e) := by
    let A : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ := B.compr₂ l
    have hi (u v w : G.Color) : A (G.ad u v) w = - A v (G.ad u w) := by
      change l (B (G.ad u v) w) = - l (B v (G.ad u w)); rw [bilinear_infinitesimal B h,map_neg]
    obtain ⟨c,hc⟩ := bilinear_real H A hi
    change A x y = _ * A e e
    rw [hc x y,hc e e,real_inner_self_eq_norm_sq,he, one_pow,mul_one,mul_comm]
  apply Complex.ext
  · rw [Complex.smul_re]; exact hs Complex.reCLM.toLinearMap
  rw [Complex.smul_im]; exact hs Complex.imCLM.toLinearMap
end YM.StressFlux
