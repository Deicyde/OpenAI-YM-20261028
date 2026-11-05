import YM.Pressure.Seeds

/-!
# Temperatures for the conditional E07 estimate

Shifting x by the *fixed* beta increment (already after choosing L) still
lets us pay the coarse temp by twice the fine temp eventually. No simplicity
premise here; even outside the simple case the averaged Casimir used in this
shift is nonnegative.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.E07

open Lattice Pressure Gauge Filter
open scoped Topology

lemma slope_nonneg (G : Gauge) : 0 ≤ G.slopeConstant := by
  have hc : 0 ≤ G.casimir := by
    let b := EuclideanSpace.basisFun G.ColorIndex ℝ
    unfold Gauge.casimir
    refine div_nonneg (neg_nonneg.mpr (Finset.sum_nonpos fun i _ => ?_)) (by positivity)
    apply neg_nonneg.mp
    change 0 ≤ G.minusKilling (b i) (b i)
    rw [minusKilling_sq (b i) b]
    positivity
  unfold slopeConstant
  positivity

lemma radiusB_eventually (N : ℕ) : ∀ᶠ x : ℝ in atTop, N ≤ radiusB x := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (N + 1 : ℝ))] with x hx
  unfold radiusB
  have h : (N : ℝ) ≤ ↑(Nat.ceil (Real.log x ^ 2)) :=
    le_trans (by have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _; nlinarith) (Nat.le_ceil _)
  exact_mod_cast h

lemma temp_nonneg (x : ℝ) : 0 ≤ temp x := by
  unfold temp; positivity

lemma temp_coarse_le (G : Gauge) (L : Side) :
    ∀ᶠ x : ℝ in atTop, temp x ≤ 2 * fiery G x L := by
  let a := G.slopeConstant * Real.log L.val
  have ha : 0 ≤ a := by
    have hL : 1 ≤ (L.val : ℝ) := by exact_mod_cast L.property
    exact mul_nonneg (slope_nonneg G) (Real.log_nonneg hL)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop a,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with x hx hs hy
  have hsinv : (Real.sqrt x)⁻¹ ≤ 2 * (Real.sqrt (x + a))⁻¹ := by
    have hh : 0 < x + a := add_pos_of_pos_of_nonneg hx ha
    have hl : Real.sqrt (x + a) ≤ 2 * Real.sqrt x := by
      nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt hh.le, Real.sqrt_pos.2 hx]
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (Real.sqrt_pos.2 hx) (Real.sqrt_pos.2 hh)).2
    rwa [one_mul]
  have he : (Real.log (Real.log x))^2 ≤ (Real.log (Real.log (x + a)))^2 := by
    apply pow_le_pow_left₀ (Real.log_nonneg hy) _
    apply Real.log_le_log (by linarith only [hy])
    exact Real.log_le_log hx (le_add_of_nonneg_right ha)
  unfold temp fiery betaF
  unfold temp
  rw [← mul_assoc]
  exact mul_le_mul hsinv (Real.exp_le_exp.mpr he) (by positivity) (by positivity)

end YM.Work.E07
