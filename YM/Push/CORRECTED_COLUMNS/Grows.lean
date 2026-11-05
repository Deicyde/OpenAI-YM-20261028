import YM.Push.CORRECTED_COLUMNS.Reprint
/-!
# Paying the A-geometry on the one calendar: preliminary asymptotics

Bounding the beta ratio over the ENTIRE stretch from `Series` on the
accepted schedule, including large L jumps – for these prices they
are controlled by `.Gentle`. Doesn't give a running-cost lemma for
the *actual restarted wire*, this is just about numbers. We don't
charge varying Stage parameters yet; use per fixed finite ν here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Grows
open Function Set Filter Lattice Wilson RG Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius

section
-- Useful log comparison parameters; all Ceils for finite radii at current beta.
def R (β : ℝ) := Nat.ceil (Real.log β ^ (2:ℕ))
def y (β : ℝ) := Real.log (Real.log β)

lemma hills (a : ℕ) (b d : ℝ) (hb : 0<b) (hd : 0<d) :
    ∀ᶠ x in atTop, (R x : ℝ)^a ≤ d* (Zone.Demand.cal x)^b := by
  have hg : Tendsto y atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hx : Tendsto (fun x => b*y x/2) atTop atTop := (hg.const_mul_atTop hb).atTop_mul_const (by positivity : 0 < (2:ℝ)⁻¹) -- div
  have hh : Tendsto (fun x => b*(y x)^2/2) atTop atTop :=
    (( (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hg).const_mul_atTop hb).atTop_mul_const (by positivity : 0 < (2:ℝ)⁻¹)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,hg.eventually_ge_atTop 1,
    hx.eventually_ge_atTop (2*a),hh.eventually_ge_atTop ((a:ℝ)*Real.log 2-Real.log d)] with x hx hg ht hj
  have hs : 0<Real.log x := lt_of_lt_of_le zero_lt_one hx
  have hl : 0<y x := lt_of_lt_of_le zero_lt_one hg
  have he := Nat.ceil_lt_add_one (sq_nonneg (Real.log x))
  have hv : (R x : ℝ) ≤ Real.exp (Real.log 2 + 2*y x) := by
    unfold y; rw [Real.exp_add,Real.exp_log (by norm_num),(show Real.exp (2*Real.log _)=(Real.exp (Real.log (Real.log x)))^2 by simpa using Real.exp_nat_mul (Real.log (Real.log x)) 2),Real.exp_log hs]
    unfold R; nlinarith
  apply (pow_le_pow_left₀ (by positivity : 0 ≤ (R x:ℝ)) hv _).trans
  erw [← Real.exp_nat_mul,Real.rpow_def_of_pos (Real.exp_pos _)]
  rw [Real.log_exp]
  rw [← Real.exp_log hd]
  rw [← Real.exp_add]; apply Real.exp_monotone
  change (a:ℝ)* (Real.log 2 + 2*y x) ≤ Real.log d+y x^2*b
  have ht : 2*a ≤ b*y x/2 := ht
  change _ ≤ b*y x^2/2 at hj
  linarith only [mul_le_mul_of_nonneg_right ht hl.le,hj]



end
section
variable {G : Gauge}
variable (A : Levels G) (H : G.Simple)
include H

lemma beta : Tendsto A.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos H))

-- Across even L jumps, coverSize^a absorbs into next side. Nat coe in statement.
lemma walls (a : ℕ) : ∀ᶠ i in atTop, A.clock.coverSize (i+1)^a ≤ 2*A.clock.coverSize i^a := by
  have hp := Real.tendsto_log_atTop.comp (beta A H)
  have ht : ∀ᶠ i in atTop, A.clock.hatBeta (i+1) ≤ 2*A.clock.hatBeta i := by
    filter_upwards [A.fits.mesh.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),A.S.divergent.eventually_gt_atTop 0] with i hi he
    have hS : Real.log (A.S.block i).val ≤ A.S.scale i := by
      have hh : Real.log (A.S.block i).val / A.S.scale i ≤ 1 := hi
      simpa using (div_le_iff₀ he).mp hh
    have hg := Gauge.slopeConstant_pos H
    unfold Calendar.hatBeta
    rw [Schedule.scale_succ]; nlinarith only [A.clock.bar_pos, mul_le_mul_of_nonneg_left hS hg.le]
  let aK (z : ℝ) := ((Real.log 2+z)^2+1)/z^2
  have hk : Tendsto (fun z : ℝ => aK z ^ a) atTop (𝓝 1) := by
    have he : Tendsto (fun z : ℝ => Real.log 2/z) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hx : Tendsto (fun z : ℝ => 1/z^2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : 2≠0))
    have hu : Tendsto aK atTop (𝓝 1) := by
      have hw := (((he.add_const 1).pow 2).add hx)
      simp only [zero_add,one_pow,add_zero] at hw
      apply hw.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with i hi
      unfold aK; field_simp
    simpa using hu.pow a
  filter_upwards [ht,(hk.comp hp).eventually (ge_mem_nhds (by norm_num : (1:ℝ)<2)),hp.eventually_gt_atTop 1] with i hi hm hj
  let x := A.clock.hatBeta i
  have hx : 0 < x := (zero_lt_one.trans (A.fits.delayed i))
  have hg : 0 < Real.log x := zero_lt_one.trans hj
  have hh : (A.clock.coverSize (i+1):ℝ) ≤ (Real.log 2+Real.log x)^2+1 := by
    have hu := Nat.ceil_lt_add_one (sq_nonneg (Real.log (A.clock.hatBeta (i+1))))
    have hw : Real.log (A.clock.hatBeta (i+1)) ≤ Real.log 2 + Real.log x :=
      (Real.log_le_log (zero_lt_one.trans (A.fits.delayed _)) hi).trans_eq (Real.log_mul (by norm_num) hx.ne')
    exact hu.le.trans (by gcongr; exact (Real.log_pos (A.fits.delayed _)).le)
  have he : (A.clock.coverSize (i+1):ℝ)^a ≤ 2*(A.clock.coverSize i:ℝ)^a := calc
    _ ≤ ((Real.log 2+Real.log x)^2+1)^a := pow_le_pow_left₀ (by positivity) hh _
    _ ≤ 2*((Real.log x)^2)^a := by
      change (((Real.log 2+Real.log x)^2+1)/(Real.log x)^2)^a ≤ 2 at hm
      rwa [div_pow,div_le_iff₀ (by positivity)] at hm
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (Nat.le_ceil _) _) (by norm_num)
  exact_mod_cast he

end
section Stretch
variable {G : Gauge} {C : Family G}

-- neighboring factor comparison from m-1 scaled to hatBeta_m



end Stretch
end YM.Push.Corrected.Grows
