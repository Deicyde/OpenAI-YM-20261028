import YM.Bid.Fuels

/-!
# I04: stop-width bookkeeping

Here the column product runs over levels `1,...,n` (not starting at `0`),
with a *separate* factor for the columns at `n`. Use a sublinear budget for
this product, along the one schedule of the given Family. `p` in `I04` is
a fixed positive real envelope prefactor, not a period index. No claim here
that the budgets buy the underlying marker estimates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.I04

open Filter RG Asymptotics
open scoped Topology BigOperators

variable {G : Gauge}

/-- The accumulated log cost of the columns, with the fine-side price even
on transitions. This uses logCost before any `Makes`/trajectory estimates. -/
theorem columns_receipt (a : Levels G) :
    (fun i => ∑ m ∈ Finset.range i, Real.log (a.params (m+1)).columns) =o[atTop] a.S.scale := by
  let f : ℕ → ℝ := fun i => ∑ m ∈ Finset.range i, Real.log (a.params (m+1)).columns
  have hf (i) : 0 ≤ f i :=
    Finset.sum_nonneg fun m _ => Real.log_nonneg (a.params (m+1)).columns_ge
  change f =o[atTop] a.S.scale
  refine isLittleO_iff.mpr ?_
  intro ε hε
  have hz : Tendsto (fun i : ℕ => ((a.clock.J (i+1) : ℝ)^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (n := 2) (by decide)).comp
        (tendsto_natCast_atTop_atTop.comp (a.fits.deep.comp (tendsto_add_atTop_nat 1))))
  -- Tail increment control and absorption of a finite prefix, as for
  -- the drift in Shoot.trajectory.
  obtain ⟨j,hj⟩ := eventually_atTop.mp (hz.eventually (ge_mem_nhds (half_pos hε)))
  have htail (i : ℕ) (hi : j ≤ i) :
      f i ≤ f j + ε/2 * (a.S.scale i - a.S.scale j) := by
    induction i, hi using Nat.le_induction with
    | base => rw [sub_self, mul_zero, add_zero]
    | succ i hi H =>
      let X := a.params (i+1)
      have hcol : Real.log X.columns ≤
          Real.log (1 + X.paths + X.width⁻¹ + X.columns + X.clip.relaxation + X.supportExponent) :=
        Real.log_le_log (lt_of_lt_of_le zero_lt_one X.columns_ge) (by
          linarith only [X.paths_pos, (inv_pos.mpr X.width_pos), X.clip.radius_pos, X.price_pos])
      have hL : 0 < Real.log (a.S.block i).val := Real.log_pos (by
        exact_mod_cast (show 1 < (a.S.block i).val from
          lt_of_lt_of_le (by norm_num) (a.S.block_large i)))
      have he : Real.log (a.params (i+1)).columns ≤ ε/2 * Real.log (a.S.block i).val :=
        hcol.trans ((div_le_iff₀ hL).mp ((a.fits.logCost i).trans (hj i hi)))
      have step : f (i+1) = f i + Real.log (a.params (i+1)).columns :=
        Finset.sum_range_succ _ _
      rw [step, Schedule.scale_succ]
      linarith only [he, H]
  have hc := (a.S.divergent.const_mul_atTop (half_pos hε)).eventually_ge_atTop (f j)
  filter_upwards [eventually_ge_atTop j, hc] with i hi hb
  have hhead : f j ≤ ε/2 * a.S.scale i := hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf i), abs_of_nonneg (Shoot.scale_nn a i)]
  linarith only [hhead, htail i hi, mul_nonneg hε.le (Shoot.scale_nn a j)]

/-- Only logarithmic costs in the hatted beta. It is affine in scale. -/
theorem hat_receipt (a : Levels G) (hG : G.Simple) :
    (fun i => Real.log (a.clock.hatBeta i)) =o[atTop] a.S.scale := by
  have ht : Tendsto a.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
  have he : (fun _ : ℕ => a.clock.bar) =o[atTop] a.S.scale :=
    (isLittleO_const_id_atTop a.clock.bar).comp_tendsto a.S.divergent
  have hf : a.clock.hatBeta =O[atTop] a.S.scale :=
    he.isBigO.add ((isBigO_refl a.S.scale _).const_mul_left G.slopeConstant)
  exact (Real.isLittleO_log_id_atTop.comp_tendsto ht).trans_isBigO hf

theorem answer : YM.Bid.I04 := by
  intro G hG p C r hp hpaid
  let a := C.path.levels
  have hc (i : ℕ) : 0 < (a.params i).columns :=
    lt_of_lt_of_le zero_lt_one (a.params i).columns_ge
  have hprod (i : ℕ) :
      0 < ∏ m ∈ Finset.range i, (a.params (m+1)).columns :=
    Finset.prod_pos fun m _ => hc (m+1)
  have hpos (i : ℕ) : 0 < Mix.envelope C p i :=
    mul_pos (mul_pos hp (hc i)) (hprod i)
  have hu (i : ℕ) : 0 < a.clock.hatBeta i := lt_trans zero_lt_one (a.fits.delayed i)
  have hg (i : ℕ) : 0 < a.clock.hatCoupling i := inv_pos.mpr (Real.sqrt_pos.2 (hu i))
  have hw (i : ℕ) : 0 < Mix.width C p r i := div_pos (pow_pos (hg i) _) (hpos i)
  refine ⟨hw, ?_⟩
  let f : ℕ → ℝ := fun i => ∑ m ∈ Finset.range i, Real.log (a.params (m+1)).columns
  have hlog (i : ℕ) : Real.log (Mix.envelope C p i) =
      Real.log p + Real.log (a.params i).columns + f i := by
    unfold Mix.envelope
    rw [Real.log_mul (mul_pos hp (hc i)).ne' (hprod i).ne', Real.log_mul hp.ne' (hc i).ne']
    rw [Real.log_prod (fun m _ => (hc (m+1)).ne')]
  let bill : ℕ → ℝ := fun i =>
    5 + Real.log p + (r/2 : ℝ) * Real.log (a.clock.hatBeta i) + 3 * f i
  have hconst : (fun _ : ℕ => 5 + Real.log p) =o[atTop] a.S.scale :=
    (isLittleO_const_id_atTop _).comp_tendsto a.S.divergent
  have hb : bill =o[atTop] a.S.scale :=
    (hconst.add ((hat_receipt a hG).const_mul_left _)).add
      ((columns_receipt a).const_mul_left _)
  intro ε hε
  filter_upwards [hb.def hε, eventually_gt_atTop 0] with i hi hx
  refine le_trans (b := bill i) ?_ ?_
  · have ht : 0 < (Nat.factorial (a.params i).order : ℝ) := by positivity
    have hfact : Real.log (Nat.factorial (a.params i).order : ℝ) ≤ Real.log (a.params i).columns :=
      Real.log_le_log ht (hpaid i)
    -- only after level zero: f i already includes the last column
    have hf : Real.log (a.params i).columns ≤ f i := by
      cases i with
      | zero => simp at hx
      | succ j =>
        unfold f
        rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_left (Finset.sum_nonneg fun m _ =>
          Real.log_nonneg (a.params (m+1)).columns_ge)
    have hl : Real.log (Mix.width C p r i) =
        -(r/2 : ℝ) * Real.log (a.clock.hatBeta i) - Real.log (Mix.envelope C p i) := by
      change Real.log (a.clock.hatCoupling i ^ r / Mix.envelope C p i) = _
      rw [Real.log_div (pow_pos (hg i) _).ne' (hpos i).ne', Real.log_pow,
        Calendar.hatCoupling, Real.log_inv, Real.log_sqrt (hu i).le]
      ring
    change 5 - Real.log (Mix.width C p r i / (Nat.factorial (a.params i).order : ℝ)) ≤ _
    rw [Real.log_div (hw i).ne' ht.ne', hl, hlog]
    unfold bill
    linarith only [hf, hfact]
  apply le_trans (Real.le_norm_self _) (le_trans hi ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Shoot.scale_nn a i)]
end YM.Work.I04
