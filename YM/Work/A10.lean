import YM.Bid.Angular

/-!
# Differentiating a Port

Use the group law only on actual group elements. First intertwine by
conjugating exponential curves, then differentiate the intertwining identity
along another exponential curve. Both differentiations of the action itself
only require derivatives at `t=0` on individual vectors.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A10

open Table Spin Org Bid NormedSpace
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L}

private def conjSkew (A : Ortho) (g : Ortho.Skew) : Ortho.Skew :=
  ⟨A.val * g.val * star A.val, by
    change star _ = -_
    have h : star g.val = -g.val := g.property
    simp only [star_mul, star_star, h, neg_mul, ← mul_assoc, mul_neg]⟩

private lemma oneParameter_conj (A : Ortho) (g : Ortho.Skew) (t : ℝ) :
    Ortho.oneParameter (conjSkew A g) t = A * Ortho.oneParameter g t * A⁻¹ := by
  apply Subtype.ext
  change exp (t • (A.val * g.val * star A.val)) = A.val * exp (t • g.val) * star A.val
  haveI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
  let w : M4ˣ := ⟨A.val, star A.val, A.property.2, A.property.1⟩
  rw [show t • (A.val * g.val * star A.val) = A.val * (t • g.val) * star A.val by simp]
  exact exp_units_conj w _

private lemma oneParameter_zero (g : Ortho.Skew) : Ortho.oneParameter g 0 = 1 := by
  apply Subtype.ext
  change exp ((0 : ℝ) • g.val) = (1 : M4)
  simp

private lemma intertwine {H : S.RealSpin} {R : Rotation S} (hp : Port R H)
    (d : ℕ) (A : Ortho) (g : Ortho.Skew) (x : S.Field d) :
    R.act d A (R.lie d g x) = R.lie d (conjSkew A g) (R.act d A x) := by
  let T := (R.act d A).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have h : HasDerivAt (fun t => R.act d A (R.act d (Ortho.oneParameter g t) x))
      (R.act d A (R.lie d g x)) 0 :=
    T.hasFDerivAt.comp_hasDerivAt 0 (hp.spinAt d g x)
  rw [show (fun t => R.act d A (R.act d (Ortho.oneParameter g t) x)) =
      (fun t => R.act d (Ortho.oneParameter (conjSkew A g) t) (R.act d A x)) from by
    funext t
    rw [← hp.sends, ← hp.sends, oneParameter_conj]
    simp [mul_assoc]] at h
  exact h.unique (hp.spinAt d (conjSkew A g) (R.act d A x))

/-- The variation of Ad along `exp(t u)`, as a derivative in the skew subspace. -/
private lemma conj_deriv (u v : Ortho.Skew) :
    HasDerivAt (fun t => conjSkew (Ortho.oneParameter u t) v) (Org.bracket u v) 0 := by
  let a := fun t => (Ortho.oneParameter u t).val
  have he : HasDerivAt a u.val 0 := by
    simpa [a, Ortho.oneParameter] using! hasDerivAt_exp_smul_const u.val (0 : ℝ)
  have h : HasDerivAt (fun t => (conjSkew (Ortho.oneParameter u t) v).val)
      (Org.bracket u v).val 0 := by
    have hz := (he.mul_const v.val).mul he.star
    have ha : a 0 = 1 := by simp [a, Ortho.oneParameter]
    change HasDerivAt (fun t => a t * v.val * star (a t))
      (u.val * v.val - v.val * u.val) 0
    have hu : star u.val = -u.val := u.property
    simpa only [ha, one_mul, star_one, hu, mul_one, mul_neg, sub_eq_add_neg] using! hz
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply tendsto_subtype_rng.mpr
  exact h.tendsto_slope_zero

/-- Evaluation of `lie` is real bilinear and continuous; bundle it
for the product rule, using finite dimensionality with the given topology. -/
private def lieC (R : Rotation S) (d : ℕ) :
    Ortho.Skew →L[ℝ] (S.Field d →L[ℝ] S.Field d) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun g => (LinearMap.toContinuousLinearMap (R.lie d g)).restrictScalars ℝ
    map_add' := fun u v => by
      apply ContinuousLinearMap.ext; intro x
      change R.lie d (u + v) x = R.lie d u x + R.lie d v x
      rw [map_add]; rfl
    map_smul' := fun r g => by
      apply ContinuousLinearMap.ext; intro x
      change R.lie d (r • g) x = r • R.lie d g x
      rw [map_smul]; rfl }

private lemma lie_brackets {H : S.RealSpin} {R : Rotation S} (hp : Port R H) :
    Brackets R.lie := by
  intro d u v
  apply LinearMap.ext
  intro x
  let f := Ortho.oneParameter u
  have hz : f 0 = 1 := oneParameter_zero _
  have h0 : conjSkew (f 0) v = v := by
    rw [hz]
    apply Subtype.ext
    change (1 : M4) * v.val * star 1 = v.val
    simp
  have hx := (lieC R d).hasDerivAt_of_bilinear
    (fun _ => conj_deriv u v) (fun _ => hp.spinAt d u x)
  change HasDerivAt (fun t => R.lie d (conjSkew (f t) v) (R.act d (f t) x))
    (R.lie d (conjSkew (f 0) v) (R.lie d u x) +
      R.lie d (Org.bracket u v) (R.act d (f 0) x)) 0 at hx
  rw [h0, hz, hp.fixes] at hx
  rw [show (fun t => R.lie d (conjSkew (f t) v) (R.act d (f t) x)) =
      (fun t => R.act d (f t) (R.lie d v x)) from
    funext fun t => (intertwine hp d (f t) v x).symm] at hx
  have hh := (hp.spinAt d u (R.lie d v x)).unique hx
  change R.lie d u (R.lie d v x) - R.lie d v (R.lie d u x) = R.lie d (Org.bracket u v) x
  rw [hh, add_sub_cancel_left]

theorem answer : YM.Bid.A10 := by
  intro G L S H R h
  exact ⟨lie_brackets h, intertwine h⟩

end YM.Work.A10
