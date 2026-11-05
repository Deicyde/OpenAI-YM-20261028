import YM.Overlay.Schedule
import YM.Pressure.Seeds


/-!
# Comparing thresholds for a fixed L

Here `x` tends along the coarse-HAT protocol. No periods or store cardinalities
enter the estimates. Use `Vac.Numbers`' pre-existing bound on the monitor, and
`Stock.stepsize` for the cover under a change of scale.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.E09
open Filter Lattice RG Pressure Asymptotics
open scoped Topology

lemma temp_pos {x : ℝ} (hx : 0 < x) : 0 < temp x := by unfold temp; positivity

lemma betaF_growth (G : Gauge) (L : Side) :
    Tendsto (fun x : ℝ => betaF G x L) atTop atTop :=
  tendsto_atTop_add_const_right _ _ tendsto_id

/-- Any fixed shift (no `Simple` assumption needed here). Estimate the log
of the threshold, using the bounded derivative of `(log v)^2` eventually in v. -/
lemma temp_ratio (k : ℝ) :
    Tendsto (fun x : ℝ => temp (x+k) / temp x) atTop (𝓝 1) := by
  let f := fun x : ℝ => Real.log x ^ 2
  let f' := fun x : ℝ => 2 * Real.log x / x
  have hf (x : ℝ) (hx : x ∈ Set.Ici (1:ℝ)) : HasDerivWithinAt f (f' x) (Set.Ici 1) x := by
    change 1 ≤ x at hx
    simpa [f, f', div_eq_mul_inv] using!
      (((Real.hasDerivAt_log (show x ≠ 0 by linarith)).pow 2).hasDerivWithinAt (s := Set.Ici 1))
  have hb (x : ℝ) (hx : x ∈ Set.Ici (1:ℝ)) : ‖f' x‖ ≤ 2 := by
    change 1 ≤ x at hx
    have hx' : 0 < x := by linarith
    unfold f'
    rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hx)) hx'.le),
      div_le_iff₀ hx']
    linarith [Real.log_le_sub_one_of_pos hx']
  have ha : Tendsto (fun x : ℝ => x+k) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hl := Real.tendsto_log_comp_add_sub_log k
  have hh : Tendsto (fun x : ℝ => f (Real.log (x+k)) - f (Real.log x)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_
      (show Tendsto (fun x : ℝ => 2 * ‖Real.log (x+k) - Real.log x‖) atTop (𝓝 0) from
        by simpa using hl.norm.const_mul 2)
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
      (Real.tendsto_log_atTop.comp ha).eventually_ge_atTop 1] with x hx hk
    exact (convex_Ici (𝕜 := ℝ) _).norm_image_sub_le_of_norm_hasDerivWithin_le hf hb hx hk
  have he (x : ℝ) (hx : 0 < x) :
      Real.log (temp x) = f (Real.log x) - Real.log x/2 := by
    unfold f temp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_inv,
      Real.log_sqrt hx.le, Real.log_exp]; ring
  have ht : Tendsto (fun x : ℝ => Real.log (temp (x+k) / temp x)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ (show Tendsto (fun x : ℝ =>
        f (Real.log (x+k)) - f (Real.log x) - (Real.log (x+k) - Real.log x)/2) atTop (𝓝 0)
      from by simpa using hh.sub (hl.div_const 2))
    filter_upwards [eventually_gt_atTop 0, ha.eventually (eventually_gt_atTop 0)] with x hx hx'
    rw [Real.log_div (temp_pos hx').ne' (temp_pos hx).ne', he x hx, he _ hx']; ring
  refine Tendsto.congr' ?_ (show Tendsto (fun x : ℝ => Real.exp (Real.log (temp (x+k)/temp x))) atTop
    (𝓝 1) from by simpa only [Real.exp_zero] using! (Real.continuous_exp.tendsto 0).comp ht)
  filter_upwards [eventually_gt_atTop 0, ha.eventually (eventually_gt_atTop 0)] with x hx hx'
  exact Real.exp_log (div_pos (temp_pos hx') (temp_pos hx))

lemma radiusB_small (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (fun x : ℝ => (radiusB x : ℝ)^n) =o[atTop] fun x : ℝ => x^r := by
  have hb : (fun x : ℝ => (radiusB x : ℝ)) =O[atTop] (fun x : ℝ => (Real.log x)^2) := by
    refine isBigO_iff.mpr ⟨2, ?_⟩
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
    simp only [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
    refine le_trans (Nat.ceil_lt_add_one (sq_nonneg _)).le ?_
    nlinarith
  refine (hb.pow n).trans_isLittleO ?_
  simpa only [pow_mul, Real.rpow_natCast] using
    (isLittleO_log_rpow_rpow_atTop ((↑(2*n) : ℝ)) hr)

lemma radiusB_shift (G : Gauge) (L : Side) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (fun x : ℝ => (radiusB x : ℝ)^n) =o[atTop] fun x : ℝ => (betaF G x L)^r := by
  let k : ℝ := G.slopeConstant * Real.log L.val
  have hb : (fun x : ℝ => (radiusB x : ℝ)) =O[atTop]
      (fun x => (radiusB (betaF G x L) : ℝ)) := by
    refine isBigO_iff.mpr ⟨2, ?_⟩
    filter_upwards [(betaF_growth G L).eventually (Stock.stepsize (-k))] with x hx
    change radiusB ((x+k)+(-k))^2 ≤ 2 * radiusB (x+k)^2 at hx
    rw [add_neg_cancel_right] at hx
    have he : (radiusB x : ℝ)^2 ≤ 2 * (radiusB (betaF G x L) : ℝ)^2 := by
      exact_mod_cast hx
    simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    nlinarith [Nat.cast_nonneg (α := ℝ) (radiusB (betaF G x L))]
  exact (hb.pow n).trans_isLittleO ((radiusB_small r hr n).comp_tendsto (betaF_growth G L))

lemma temp_cost (p : ℝ) (hp : 0 < p) : ∀ᶠ x : ℝ in atTop,
    temp x ≤ x ^ (-(1/2 : ℝ)+p) := by
  filter_upwards [Vac.Numbers.cost 1 p hp, eventually_gt_atTop 0] with x h hx
  rw [Real.rpow_one] at h
  rw [Real.rpow_add hx, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_left h (by positivity)

lemma radiusB_temp (n : ℕ) :
    Tendsto (fun x : ℝ => (radiusB x : ℝ)^n * temp x) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (radiusB_small (1/4) (by norm_num) n).tendsto_div_nhds_zero
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have := temp_pos hx
    positivity
  filter_upwards [eventually_gt_atTop 0, temp_cost (1/4) (by norm_num)] with x hx ht
  rw [show -(1/2:ℝ)+1/4 = -(1/4) by norm_num, Real.rpow_neg hx.le] at ht
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left ht (by positivity)

lemma largeT_eq (G : Gauge) (L : Side) (x : ℝ) (hx : 0 ≤ betaF G x L) :
    largeT G x L = (betaF G x L)^(-(49/100:ℝ)) := by
  rw [largeT, Real.sqrt_eq_rpow, ← Real.rpow_neg hx, ← Real.rpow_mul hx]
  norm_num

/-- `B^n * t/T → 0` at fixed data. Spend after fixing L, not before. -/
lemma radiusB_fiery_largeT (G : Gauge) (L : Side) (n : ℕ) :
    Tendsto (fun x : ℝ => (radiusB x : ℝ)^n * (fiery G x L / largeT G x L)) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (radiusB_shift G L (1/200) (by norm_num) n).tendsto_div_nhds_zero
  · filter_upwards [(betaF_growth G L).eventually (eventually_gt_atTop 0)] with x hx
    unfold fiery; rw [largeT_eq _ _ _ hx.le]
    have ht := temp_pos hx
    positivity
  filter_upwards [(betaF_growth G L).eventually (eventually_gt_atTop 0),
    (betaF_growth G L).eventually (temp_cost (1/200) (by norm_num))] with x hx hy
  change (_:ℝ)^_ * (_ / _) ≤ (radiusB x : ℝ)^n / _
  rw [div_eq_mul_inv ((radiusB x : ℝ)^n)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [largeT_eq _ _ _ hx.le]
  apply le_trans (div_le_div_of_nonneg_right hy (by positivity))
  apply le_of_eq
  rw [← Real.rpow_sub hx, ← Real.rpow_neg hx.le]; norm_num

end YM.Work.E09
