import YM.Bid.Angular

/-!
# Algebraic generation of the actual `Ortho`

Use Mathlib's generation by reflections on `E4`. Every hyperplane reflection there
is rotation-conjugate to a coordinate mirror. To realize the conjugator in the
specified subgroup, we align the normal vector by elementary rotations, working
out the actions of those `Ortho.oneParameter`s on vectors.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A13

open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace

lemma hasDerivAt_move (g : Ortho.Skew) (v : E4) (t : ℝ) :
    HasDerivAt (fun u => Ortho.move (Ortho.oneParameter g u) v)
      (M4.move g.val (Ortho.move (Ortho.oneParameter g t) v)) t := by
  unfold Ortho.move
  rw [← M4.move_mul]
  let f : M4 →ₗ[ℝ] E4 := (LinearMap.applyₗ v).comp Matrix.toEuclideanLin.toLinearMap
  exact (LinearMap.toContinuousLinearMap f).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' g.val t)

lemma hasDerivAt_coord (g : Ortho.Skew) (v : E4) (k : Axis) (t : ℝ) :
    HasDerivAt (fun u => Ortho.move (Ortho.oneParameter g u) v k)
      (M4.move g.val (Ortho.move (Ortho.oneParameter g t) v) k) t :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_move g v t)

lemma plane_field_apply {i j : Axis} (hij : i ≠ j) (v : E4) (k : Axis) :
    M4.move (Ortho.plane i j).val v k =
      if k = i then v j else if k = j then -(v i) else 0 := by
  change ((Matrix.single i j (1 : ℝ) - Matrix.single j i 1) *ᵥ v.ofLp) k = _
  rw [Matrix.sub_mulVec, Matrix.single_mulVec, Matrix.single_mulVec]
  by_cases hi : k = i
  · subst k; simp [hij]
  by_cases hj : k = j
  · subst k; simp [hi]
  simp [hi, hj]

lemma oneParameter_zero (g : Ortho.Skew) : Ortho.oneParameter g 0 = 1 := by
  apply Subtype.ext
  change NormedSpace.exp ((0 : ℝ) • g.val) = 1
  simp

private lemma equals_at_zero {f : ℝ → ℝ} (hf : ∀ u, HasDerivAt f 0 u) (t : ℝ) : f t = f 0 :=
  is_const_of_deriv_eq_zero (fun u => (hf u).differentiableAt) (fun u => (hf u).deriv) t 0

/-- Note the signs: `plane i j` rotates toward `i` from `j`. -/
lemma plane_givens {i j : Axis} (hij : i ≠ j) (v : E4) (t : ℝ) :
    let w := Ortho.move (Ortho.oneParameter (Ortho.plane i j) t) v
    w i = Real.cos t * v i + Real.sin t * v j ∧
    w j = Real.cos t * v j - Real.sin t * v i ∧
    ∀ k : Axis, k ≠ i → k ≠ j → w k = v k := by
  let g := Ortho.plane i j
  let y (k : Axis) (u : ℝ) := Ortho.move (Ortho.oneParameter g u) v k
  have he (k) : y k 0 = v k := by simp [y, oneParameter_zero]
  have h (k u) : HasDerivAt (y k)
      (if k = i then y j u else if k = j then -(y i u) else 0) u := by
    simpa only [y, g, plane_field_apply hij] using hasDerivAt_coord (Ortho.plane i j) v k u
  have hi u : HasDerivAt (y i) (y j u) u := by simpa using h i u
  have hj u : HasDerivAt (y j) (-(y i u)) u := by simpa [Ne.symm hij] using h j u
  -- Multiply by the inverse rotation: both resulting coordinates are constant.
  have h₁ (u) : HasDerivAt
      (fun s => Real.cos s * y i s - Real.sin s * y j s) 0 u := by
    refine (((Real.hasDerivAt_cos u).fun_mul (hi u)).fun_sub
      ((Real.hasDerivAt_sin u).fun_mul (hj u))).congr_deriv ?_
    ring
  have h₂ (u) : HasDerivAt
      (fun s => Real.sin s * y i s + Real.cos s * y j s) 0 u := by
    refine (((Real.hasDerivAt_sin u).fun_mul (hi u)).fun_add
      ((Real.hasDerivAt_cos u).fun_mul (hj u))).congr_deriv ?_
    ring
  have ha : Real.cos t * y i t - Real.sin t * y j t = v i := by
    simpa [he] using equals_at_zero h₁ t
  have hb : Real.sin t * y i t + Real.cos t * y j t = v j := by
    simpa [he] using equals_at_zero h₂ t
  have hc := Real.sin_sq_add_cos_sq t
  change y i t = _ ∧ y j t = _ ∧ ∀ k : Axis, k ≠ i → k ≠ j → y k t = v k
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -(y i t) * hc + Real.cos t * ha + Real.sin t * hb
  · linear_combination -(y j t) * hc - Real.sin t * ha + Real.cos t * hb
  · intro k hki hkj
    refine (equals_at_zero (f := y k) ?_ t).trans (he k)
    intro u
    simpa [hki, hkj] using h k u

lemma plane_eliminates {i j : Axis} (hij : i ≠ j) (v : E4) :
    ∃ t : ℝ, Ortho.move (Ortho.oneParameter (Ortho.plane i j) t) v j = 0 := by
  let z : ℂ := ⟨v i, v j⟩
  refine ⟨z.arg, ?_⟩
  rw [(plane_givens hij v z.arg).2.1]
  have hs : ‖z‖ * Real.sin z.arg = v j := Complex.norm_mul_sin_arg z
  have hc : ‖z‖ * Real.cos z.arg = v i := Complex.norm_mul_cos_arg z
  rw [← hs, ← hc]; ring

/-- Zero any set of non-pivot coordinates, by successive left actions. -/
lemma squash (i : Axis) (v : E4) (s : Finset Axis) (h : i ∉ s) :
    ∃ g ∈ YM.Bid.AxisGens, ∀ j ∈ s, Ortho.move g v j = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, YM.Bid.AxisGens.one_mem, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨hij, his⟩ := (show i ≠ j ∧ i ∉ s by simpa using h)
    obtain ⟨b, hb, hbs⟩ := ih his
    obtain ⟨t, ht⟩ := plane_eliminates hij (Ortho.move b v)
    let r := Ortho.oneParameter (Ortho.plane i j) t
    have hr : r ∈ YM.Bid.AxisGens := Subgroup.subset_closure (Or.inr ⟨_, t, rfl⟩)
    refine ⟨r * b, YM.Bid.AxisGens.mul_mem hr hb, ?_⟩
    intro k hk
    rw [Ortho.move_mul]
    rcases Finset.mem_insert.mp hk with he | hm
    · subst k; exact ht
    have hki : k ≠ i := fun e => his (e ▸ hm)
    have hkj : k ≠ j := fun e => hj (e ▸ hm)
    exact ((plane_givens hij (Ortho.move b v) t).2.2 k hki hkj).trans (hbs k hm)

lemma align (i : Axis) (v : E4) :
    ∃ g ∈ YM.Bid.AxisGens, ∃ c : ℝ, Ortho.move g v = c • basis i := by
  obtain ⟨g, hg, hall⟩ := squash i v (Finset.univ.erase i) (by simp)
  refine ⟨g, hg, Ortho.move g v i, PiLp.ext ?_⟩
  intro k
  by_cases h : k = i
  · subst k; simp
  simp [h, hall k (by simp [h])]

def motionHom : Ortho →* (E4 ≃ₗᵢ[ℝ] E4) where
  toFun := Ortho.motion
  map_one' := LinearIsometryEquiv.ext (fun x => Ortho.move_one x)
  map_mul' r s := LinearIsometryEquiv.ext (fun x => Ortho.move_mul r s x)

lemma motionHom_injective : Function.Injective motionHom := by
  intro r s h
  apply Ortho.ext
  intro x
  exact congr_arg (fun f : E4 ≃ₗᵢ[ℝ] E4 => f x) h

lemma motionHom_mirror (i : Axis) :
    motionHom (Signed.reflect i) = (ℝ ∙ basis i)ᗮ.reflection := by
  apply LinearIsometryEquiv.ext; intro x
  change Ortho.move _ x = _
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  apply PiLp.ext; intro k
  rw [Signed.mirrored]
  by_cases hi : k = i
  · subst k; simp; ring
  simp [hi]

/-- All (genuine) hyperplane reflections come from conjugating just one mirror. -/
lemma reflection_conjugate (i : Axis) {v : E4} (hv : v ≠ 0) :
    ∃ g ∈ YM.Bid.AxisGens,
      motionHom (g⁻¹ * Signed.reflect i * g) = (ℝ ∙ v)ᗮ.reflection := by
  obtain ⟨g, hg, c, hc⟩ := align i v
  refine ⟨g, hg, ?_⟩
  let f := motionHom g
  have he : f v = c • basis i := hc
  have hcn : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hv (f.injective (by simpa using he))
  have ht : (ℝ ∙ v)ᗮ.map (f.toLinearEquiv : E4 →ₗ[ℝ] E4) = (ℝ ∙ basis i)ᗮ := by
    rw [Submodule.map_orthogonal_equiv, Submodule.map_span, Set.image_singleton]
    change (ℝ ∙ f v)ᗮ = _
    rw [he, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hcn)]
  have hm : (ℝ ∙ basis i)ᗮ.reflection = f.symm.trans ((ℝ ∙ v)ᗮ.reflection.trans f) :=
    (congrArg (fun A : Submodule ℝ E4 => A.reflection) ht.symm).trans
      (Submodule.reflection_map f (ℝ ∙ v)ᗮ)
  rw [map_mul, map_mul, map_inv, motionHom_mirror]
  change f⁻¹ * (ℝ ∙ basis i)ᗮ.reflection * f = (ℝ ∙ v)ᗮ.reflection
  rw [hm]
  apply LinearIsometryEquiv.ext; intro x
  change f.symm (f ((ℝ ∙ v)ᗮ.reflection (f.symm (f x)))) = _
  simp

lemma reflection_mem (v : E4) :
    (ℝ ∙ v)ᗮ.reflection ∈ YM.Bid.AxisGens.map motionHom := by
  by_cases hv : v = 0
  · subst v
    have he : (ℝ ∙ (0 : E4))ᗮ.reflection = 1 := by
      apply LinearIsometryEquiv.ext; intro x
      apply Submodule.reflection_mem_subspace_eq_self
      simp
    rw [he]; exact Subgroup.one_mem _
  obtain ⟨g, hg, he⟩ := reflection_conjugate timeAxis hv
  have hr : Signed.reflect timeAxis ∈ YM.Bid.AxisGens :=
    Subgroup.subset_closure (Or.inl ⟨Signed.mirror timeAxis, rfl⟩)
  refine Subgroup.mem_map.mpr ⟨_, ?_, he⟩
  exact YM.Bid.AxisGens.mul_mem (YM.Bid.AxisGens.mul_mem (YM.Bid.AxisGens.inv_mem hg) hr) hg

theorem answer : YM.Bid.A13 := by
  have h : ⊤ ≤ YM.Bid.AxisGens.map motionHom := by
    rw [← LinearIsometryEquiv.reflections_generate]
    apply (Subgroup.closure_le _).mpr
    rintro r ⟨v, rfl⟩
    exact reflection_mem v
  apply (Subgroup.eq_top_iff' _).mpr
  intro g
  obtain ⟨b, hb, he⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_top (motionHom g)))
  rwa [← motionHom_injective he]

end YM.Work.A13
