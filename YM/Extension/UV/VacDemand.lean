import YM.Extension.UV.CouplingScales
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Opening
/-! Amplitude calibration budget on the real histories. Not a derivative estimate; a further
step proof needs common prescriptions and signed/holomorphic majorants. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
namespace YM.Extension.UV
open RG.Shoot Filter Function Lattice RG RG.Supply AnalyticBridge VerifiedReset
variable {G:Gauge}


def waitAmount {G} (s:Sheet G) (j:ℕ):= max (Time.credit G (s.profile j)) (Time.credit G (s.profile (j-1))) * 4
lemma waitAbove {G : Gauge} (s:Sheet G) : ∃ f : ℕ→ℝ,∀ i x, f i ≤ x → waitAmount s i ≤ x ^ (1/20:ℝ):=by
  choose f h using fun i=> eventually_atTop.mp ((tendsto_rpow_atTop (show (0:ℝ)<1/20 by norm_num)).eventually_ge_atTop (waitAmount s i))
  exact ⟨f,h⟩

def CreditScale (a:Levels G) i:= Time.credit G (a.params i) * (a.clock.allowance i)
lemma demand_credits {s:Sheet G} {w:Rolls s} {Θ:Protection w} {W:Delays Θ} {Y : Bar W} {I:Wait Y} {a:Levels G}
    (h:Paid I a) (hx:(waitAbove s).choose ≤ W.betaEntry) i: Time.credit G (a.params i) * 4 ≤ a.clock.hatBeta i ^ (1/20:ℝ):= by
  have he := (waitAbove s).choose_spec (a.clock.J (i+1)) _ ((hx _).trans (h.pays i))
  have hp:= h.stage
  have hK := a.fits.mono (Nat.le_succ i)
  have hK' := a.fits.stepSlow i
  change a.clock.J (i+1) ≤ a.clock.J i+1 at hK'
  change a.clock.J i ≤ a.clock.J (i+1) at hK
  have hq : a.params i=s.profile (a.clock.J i) := by unfold Levels.params Calendar.params; rw [hp]
  rw [hq]
  apply le_trans _ he; unfold waitAmount
  rcases (show a.clock.J i = a.clock.J (i+1) ∨ a.clock.J i = a.clock.J (i+1)-1 by omega) with hs|hs <;> rw [hs] <;> [exact mul_le_mul_of_nonneg_right (le_max_left ..) (by norm_num);exact mul_le_mul_of_nonneg_right (le_max_right ..) (by norm_num)]

lemma allowance_eq (a:Levels G) i: a.clock.allowance i = (a.clock.hatBeta i)^(-(11:ℝ)/10):= by
  let x := a.clock.hatBeta i
  have hx : 0≤x:= (by have he:=a.fits.delayed i; dsimp[x]; linarith)
  have he : (Real.sqrt x)⁻¹=x^(-(1/2:ℝ)) := by rw [Real.rpow_neg hx,← Real.sqrt_eq_rpow]
  change ((Real.sqrt x)⁻¹)^(11/5:ℝ)= _
  rw [he,← Real.rpow_mul hx]; unfold x; norm_num
lemma threshold_large (a:Levels G) i : (a.clock.hatBeta i)⁻¹ ≤ (a.budget i).threshold^2 := by
  let x := a.clock.hatBeta i
  let y := a.clock.hatCoupling i
  have he := a.fits.delayed i
  have hy : 1≤a.clock.monitor i:= Real.one_le_exp_iff.mpr (sq_nonneg _)
  change x⁻¹ ≤ (y*a.clock.monitor i)^2
  have hh : y^2=x⁻¹:= by dsimp [y,x,Calendar.hatCoupling]; rw [inv_pow, Real.sq_sqrt (by linarith)]
  rw [← hh,mul_pow]; apply le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hy)

lemma real_budget_capacity {a:Levels G} {T:Recipe a} {f : ℕ→∀ p,Trail a p} {i : ℕ} (η : NumericAdmission a T f)
    (h:Time.credit G (a.params i) * 4 ≤ a.clock.hatBeta i ^ (1/20:ℝ)) {v:ℝ} (he : (a.budget i).threshold^2 * |v| ≤ CreditScale a i):
     |v| ≤ capacity (a.clock.hatBeta (i+1)):= by
  let y:= a.clock.hatBeta i
  have hv : 0<y:=by exact zero_lt_one.trans (η.positive _)
  have hh : |v| ≤ CreditScale a i * y := by
    apply le_of_mul_le_mul_left _ (show 0<y⁻¹ by positivity)
    rw [mul_left_comm y⁻¹,inv_mul_cancel₀ hv.ne',mul_one]
    exact (mul_le_mul_of_nonneg_right (threshold_large ..) (by positivity)).trans he
  rw [CreditScale,allowance_eq,show (a.clock.hatBeta i)=y by rfl,mul_assoc,← Real.rpow_add_one hv.ne'] at hh
  have hY : capacity (2*y) ≤ capacity (a.clock.hatBeta (i+1)) := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans (η.positive _)) (η.near i) (by norm_num)
  apply (hh.trans _).trans hY
  unfold capacity; rw [Real.mul_rpow (by norm_num) hv.le]
  have h2:= (Real.rpow_le_rpow_of_exponent_le (x:=2) (by norm_num) (by norm_num : (-1:ℝ) ≤ (-1:ℝ)/20))
  rw [Real.rpow_neg_one] at h2
  calc
    _ ≤ (y^(1/20:ℝ)/4)*(y^(-(11:ℝ)/10 + 1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (1/4:ℝ)*y^(-(1:ℝ)/20)  := by
      rw [div_mul_eq_mul_div,← Real.rpow_add hv,show (1/20+(-(11:ℝ)/10+1):ℝ)=-(1:ℝ)/20 by ring]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num at h2; nlinarith) (by positivity)
end YM.Extension.UV
