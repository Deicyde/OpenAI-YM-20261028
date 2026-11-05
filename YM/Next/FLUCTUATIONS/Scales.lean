import YM.Next.FLUCTUATIONS.Defs
import YM.Work.E09.Scales


/-!
# Delay prices: fixed-L, threshold in coarse HAT units

B grows with coarse x. `fiery` is `temp (betaF G x L)`.
The T scale to the *first* power isn't small compared with fiery;
need its square, or the exponential tail in B. Post-L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Pressure.Stores Precision
open scoped Topology BigOperators
variable (G : Gauge) (L : Side)
open Work.E09

private lemma temp_ge {x : ℝ} (hx : 0≤x) : x ^ (-(1/2:ℝ)) ≤ temp x := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]
  unfold temp
  exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg _))

lemma radius_largeT (n : ℕ) :
    Tendsto (fun x : ℝ => (radiusB x : ℝ)^n * largeT G x L) atTop (𝓝 0) := by
  refine ((radiusB_shift G L (49/100) (by norm_num) n).tendsto_div_nhds_zero).congr' ?_
  filter_upwards [(betaF_growth G L).eventually (eventually_ge_atTop 0)] with x hx
  rw [largeT_eq _ _ _ hx, Real.rpow_neg hx,div_eq_mul_inv]

lemma radius_sq_largeT_fiery (n : ℕ) :
    Tendsto (fun x : ℝ => (radiusB x : ℝ)^n * largeT G x L^2 / fiery G x L) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ ((radiusB_shift G L (48/100) (by norm_num) n).tendsto_div_nhds_zero)
  · filter_upwards [(betaF_growth G L).eventually (eventually_gt_atTop 0)] with x hx
    unfold fiery; have hh := temp_pos hx; positivity
  filter_upwards [(betaF_growth G L).eventually (eventually_gt_atTop 0)] with x hx
  let s := betaF G x L
  have hs : 0 < s := hx
  calc
    _ ≤ (radiusB x:ℝ)^n * largeT G x L^2 / s ^ (-(1/2:ℝ)) := by
      gcongr; exact temp_ge hx.le
    _ = (radiusB x:ℝ)^n / s ^ (48/100:ℝ) := by
      rw [mul_div_assoc, largeT_eq _ _ _ hx.le, sq,
        ← Real.rpow_add hx,← Real.rpow_sub hx]
      rw [show -(49/100:ℝ)+ -(49/100) - -(1/2) = -(48/100) by norm_num, Real.rpow_neg hx.le,
        div_eq_mul_inv, div_eq_mul_inv]

lemma tail_delay (τ : ℝ) (ht : 0<τ) : ∀ᶠ x : ℝ in atTop,
    Real.exp (-τ*till x) ≤ (betaF G x L)⁻¹ := by
  -- b = log x. The shifted inverse power costs at most 2b in the exponent.
  let k : ℝ := G.slopeConstant * Real.log (L.val:ℝ)
  filter_upwards [(betaF_growth G L).eventually (eventually_gt_atTop 0), eventually_gt_atTop (2:ℝ),
    eventually_gt_atTop k,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (200000/τ+100000:ℝ))] with x h hx hx' hb
  rw [show (betaF G x L)⁻¹ = Real.exp (-(Real.log (betaF G x L))) by rw [Real.exp_neg, Real.exp_log h]]
  apply Real.exp_monotone
  let b := Real.log x
  have hk : Real.log (betaF G x L) ≤ 2*b := calc
    _ ≤ Real.log (x^2) := Real.log_le_log h (show x+k ≤ x^2 by nlinarith)
    _ = _ := by rw [Real.log_pow]; norm_num [b]
  have he : radiusB x ≤ 100000 * till x + 100000 := by unfold till; omega
  have hl : b^2 ≤ (100000:ℝ)*(till x:ℝ)+100000 := le_trans (Nat.le_ceil _) (by exact_mod_cast he)
  have hh : 0 < b := Real.log_pos (by linarith)
  have hp : 200000 + τ*100000 ≤ τ*b := by
    have he : 200000/τ ≤ b-100000 := by dsimp only [b]; linarith
    have hv := (div_le_iff₀ ht).mp he
    linarith
  have hv : 1 ≤ b := by
    have hf : 0 ≤ 200000/τ := by positivity
    unfold b; linarith
  nlinarith [mul_le_mul_of_nonneg_right hp hh.le, mul_le_mul_of_nonneg_left hl ht.le,
    mul_le_mul_of_nonneg_left hv ht.le]

lemma radius_tail_fiery (τ : ℝ) (ht : 0<τ) (n : ℕ) :
    Tendsto (fun x : ℝ => (radiusB x : ℝ)^n * Real.exp (-τ*till x) / fiery G x L) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ ((radiusB_shift G L (1/2) (by norm_num) n).tendsto_div_nhds_zero)
  · filter_upwards [(betaF_growth G L).eventually (eventually_gt_atTop 0)] with x hx
    unfold fiery; have hh := temp_pos hx; positivity
  filter_upwards [(betaF_growth G L).eventually (eventually_gt_atTop 0),tail_delay G L τ ht] with x hx hv
  let s := betaF G x L
  have he : 0<s := hx
  calc
    _ ≤ (radiusB x:ℝ)^n * s⁻¹ / s ^ (-(1/2:ℝ)) := by
      gcongr; exact temp_ge hx.le
    _ = (radiusB x:ℝ)^n / s ^ (1/2:ℝ) := by
      rw [mul_div_assoc,show s⁻¹ = s ^ (-1:ℝ) from (Real.rpow_neg_one s).symm,
        ← Real.rpow_sub he, show (-1:ℝ)- -(1/2) = -(1/2) by norm_num,
        Real.rpow_neg he.le, div_eq_mul_inv, div_eq_mul_inv]

include G L in
lemma radius_tail (τ : ℝ) (ht : 0<τ) (n : ℕ) :
    Tendsto (fun x : ℝ => (radiusB x : ℝ)^n * Real.exp (-τ*till x)) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_
    ((radiusB_shift G L 1 (by norm_num) n).tendsto_div_nhds_zero)
  filter_upwards [tail_delay G L τ ht] with x hx
  simpa only [div_eq_mul_inv,Real.rpow_one] using
    mul_le_mul_of_nonneg_left hx (show 0 ≤ (radiusB x:ℝ)^n by positivity)

-- Chord size in Stitches
-- use casts to fix the h scale across both delays.

def stitchCost (C : ℝ) (x : ℝ) := C*(radiusB x:ℝ)^10 * largeT G x L

lemma radius_stitch (C : ℝ) (n : ℕ) :
    Tendsto (fun x : ℝ => (radiusB x:ℝ)^n * stitchCost G L C x) atTop (𝓝 0) := by
  have he := (radius_largeT G L (n+10)).const_mul C
  rw [mul_zero] at he
  exact he.congr (fun x => by unfold stitchCost; rw [pow_add]; ring)

lemma radius_sq_stitch_fiery (C : ℝ) (n : ℕ) :
    Tendsto (fun x : ℝ => (radiusB x:ℝ)^n * (stitchCost G L C x)^2 / fiery G x L) atTop (𝓝 0) := by
  have he := (radius_sq_largeT_fiery G L (n+20)).const_mul (C^2)
  rw [mul_zero] at he
  exact he.congr (fun x => by unfold stitchCost; rw [pow_add]; ring)

lemma radius_stitch_errors (C τ : ℝ) (hC : 0<C) (ht : 0<τ) (n : ℕ) :
    let w := stitchCost G L C
    let e := fun x => widen (till x) (w x) τ
    Tendsto (fun x => (radiusB x:ℝ)^n * e x) atTop (𝓝 0) ∧
      Tendsto (fun x => (radiusB x:ℝ)^n * w x * e x / fiery G x L) atTop (𝓝 0) := by
  intro w e
  have hp := (betaF_growth G L).eventually (eventually_gt_atTop 0)
  have hw x (hh : 0<betaF G x L) : 0 ≤ w x := by
    unfold w stitchCost; rw [largeT_eq _ _ _ hh.le]; positivity
  have he x (hh : 0<betaF G x L) : 0≤e x := widen_nonneg _ (hw x hh)
  let B := fun x : ℝ => (radiusB x:ℝ)
  let E := fun x => Real.exp (-τ*till x)
  have hb x (hh : 0<betaF G x L) : e x ≤ (1+B x)*w x + E x := by
    unfold e widen
    have hx : (till x : ℝ) ≤ B x := by unfold B; exact_mod_cast Nat.div_le_self (radiusB x) 100000
    exact add_le_add_left (mul_le_mul_of_nonneg_right (add_le_add_right hx _) (hw x hh)) _
  constructor
  · have ht' := ((radius_stitch G L C n).add (radius_stitch G L C (n+1))).add (radius_tail G L τ ht n)
    simp only [add_zero] at ht'
    refine squeeze_zero' ?_ ?_ ht'
    · filter_upwards [hp] with x hh
      exact mul_nonneg (by positivity) (he x hh)
    filter_upwards [hp] with x hh
    exact (mul_le_mul_of_nonneg_left (hb x hh) (show 0 ≤ (radiusB x:ℝ)^n by positivity)).trans_eq
      (by dsimp only [e,w,B,E]; rw [pow_succ]; ring)
  have hw' : Tendsto w atTop (𝓝 0) := by simpa only [pow_zero,one_mul,w] using radius_stitch G L C 0
  have ht' := ((radius_sq_stitch_fiery G L C n).add (radius_sq_stitch_fiery G L C (n+1))).add
    (hw'.mul (radius_tail_fiery G L τ ht n))
  simp only [mul_zero,add_zero] at ht'
  refine squeeze_zero' ?_ ?_ ht'
  · filter_upwards [hp] with x hh
    have hv := hw x hh; have ht := he x hh
    unfold fiery; have hs := temp_pos hh; positivity
  filter_upwards [hp] with x hh
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hb x hh)
    (mul_nonneg (show 0 ≤ (radiusB x:ℝ)^n by positivity) (hw x hh))) (temp_pos hh).le).trans_eq
    (by dsimp only [w,B,E,fiery]; rw [pow_succ]; ring)
end YM.Next.Fluctuations
