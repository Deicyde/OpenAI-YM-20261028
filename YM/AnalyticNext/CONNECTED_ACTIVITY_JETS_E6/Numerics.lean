import YM.Push.ABSOLUTE_SUMS.Fees
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Work.G07.Stencil

/-!
# HAT bills for real connected-activity estimates

Local notation/tools for *uniform in volume*, post-`L,W` prices. Hatted variables
at x coarse; V threshold from x, fine tests from `betaF G x L`. Estimates
stated as upper powers still require a strict reserve when going on to use an
eventual inequality. In particular a `Rate 0` cost cannot in general be paid
from a power of `p`, only of βhat. These are not schedule/feasibility proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Lattice RG Pressure Push.AbsoluteSums
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators

/-- Estimate at every strictly looser βhat power. Allows βhat^{o(1)} losses;
fixed AFTER choosing L, thresholds independent of the period. No sign clause. -/
def Rate (G : Gauge) (L : Side) (a : ℝ) (w : ℝ → ℝ) : Prop :=
    ∀ v > a, ∀ᶠ x : ℝ in atTop, |w x| ≤ betaF G x L ^ v

namespace Rate
variable {G : Gauge} {L : Side} {a b r : ℝ} {w v u : ℝ → ℝ}

theorem weaken (h : Rate G L a w) (hp : a ≤ b) : Rate G L b w := fun _ hx => h _ (hp.trans_lt hx)

theorem compare (h : Rate G L a w) (hp : ∀ᶠ x in atTop, |v x| ≤ |w x|) : Rate G L a v := by
  intro b hb
  filter_upwards [hp,h b hb] with x hx ht using hx.trans ht

theorem congr (h : Rate G L a w) (hp : v =ᶠ[atTop] w) : Rate G L a v :=
  h.compare (hp.mono fun x hx => by rw [hx])

theorem const (c : ℝ) : Rate G L 0 (fun _ => c) := by
  intro b hb
  exact ((tendsto_rpow_atTop hb).comp (Work.E09.betaF_growth G L)).eventually_ge_atTop _

theorem mul (h : Rate G L a w) (k : Rate G L b v) : Rate G L (a+b) (fun x => w x*v x) := by
  intro s hs
  let d := (s-(a+b))/2
  have he : 0 < d := half_pos (sub_pos.mpr hs)
  have hy : a+d+(b+d)=s := by unfold d; ring
  filter_upwards [h (a+d) (by linarith),k (b+d) (by linarith), Delay.shift_pos G L] with x hx ht hb
  rw [abs_mul, ← hy, Real.rpow_add hb]; exact mul_le_mul hx ht (abs_nonneg _) (by positivity)

theorem mul_left (h : Rate G L a w) (c : ℝ) : Rate G L a (fun x => c * w x) := by
  simpa only [zero_add] using ((Rate.const c).mul h)

theorem mul_right (h : Rate G L a w) (c : ℝ) : Rate G L a (fun x => w x * c) := by
  simpa only [add_zero] using h.mul (Rate.const c)

theorem add (h : Rate G L a w) (k : Rate G L a v) : Rate G L a (fun x => w x + v x) := by
  intro s hs
  let e := (s-a)/2
  have he : 0 < e := half_pos (sub_pos.mpr hs)
  have hu : a+e+e=s := by unfold e; ring
  filter_upwards [h (a+e) (by linarith), k (a+e) (by linarith), Delay.shift_pos G L,
    Rate.const (G := G) (L := L) (2:ℝ) e he] with x hx hy hp hk
  let H := betaF G x L
  have hz : 2 ≤ H^e := by simpa only [abs_of_pos (by norm_num : 0 < (2:ℝ))] using! hk
  refine ((abs_add_le ..).trans (add_le_add hx hy)).trans ?_
  rw [← hu, Real.rpow_add hp (a+e) e,← mul_two]
  exact mul_le_mul_of_nonneg_left hz (Real.rpow_nonneg hp.le _)

theorem pow (h : Rate G L a w) (d : ℕ) : Rate G L (a*d) (fun x => w x^d) := by
  induction d with
  | zero => simpa only [Nat.cast_zero, mul_zero,pow_zero] using Rate.const (G := G) (L := L) 1
  | succ n ih => simpa only [pow_succ,Nat.cast_succ,mul_add,mul_one] using! ih.mul h

theorem power : Rate G L a (fun x => betaF G x L ^ a) := by
  intro b hb
  filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop 1] with x hx
  rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact Real.rpow_le_rpow_of_exponent_le hx.le hb.le

theorem hat : Rate G L 1 (fun x => betaF G x L) := by
  simpa only [Real.rpow_one] using Rate.power (G:=G) (L:=L) (a:=1)

theorem bill : Rate G L 0 (Delay.bill G L) := by
  intro b hb
  filter_upwards [Fees.growth G L hb (show 0 ≤ (1 : ℝ) by norm_num) 0 1]
    with x hx
  simpa only [abs_of_nonneg (zero_le_one.trans (Delay.bill_ge G L x)), one_mul,pow_one,
    Real.rpow_zero,mul_one] using! hx

theorem rpow_monitor (d : ℝ) : Rate G L 0 (fun x => Delay.fineMonitor G L x ^ d) := by
  intro b hb
  filter_upwards [Fees.growth G L hb (show 0 ≤ (1 : ℝ) by norm_num) d 0] with x hx
  simpa only [abs_of_nonneg (Real.rpow_nonneg (Delay.monitor_pos G L x).le _),one_mul,pow_zero] using! hx

theorem monitor : Rate G L 0 (Delay.fineMonitor G L) := by
  simpa only [Real.rpow_one] using rpow_monitor (G := G) (L := L) 1

lemma radius_price : Rate G L 0 (fun x : ℝ => (radiusB x:ℝ)) := by
  refine bill.compare (Eventually.of_forall ?_)
  intro x
  rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (zero_le_one.trans (Delay.bill_ge G L x))]
  unfold Delay.bill; linarith [sq_nonneg (Real.log (betaF G x L))]

lemma flame : Rate G L (-(1/2)) (fun x => fiery G x L) := by
  have he := Rate.mul (w := fun x => betaF G x L ^ (-(1/2:ℝ))) Rate.power Rate.monitor
  rw [add_zero] at he
  refine he.congr ?_
  filter_upwards [Delay.shift_pos G L] with x hx
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  rfl

/-- The true-length truncation price . -/
lemma cutoff {δ : ℝ} (hδ : 0 < δ) : Rate G L a (fun x => Real.exp (-δ*Stores.till x)) := by
  intro b hb
  let N := max (-b) 1
  have h1 : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_right ..)
  filter_upwards [Fees.route_tail_decay G L hδ h1,
    (Work.E09.betaF_growth G L).eventually_gt_atTop 1] with x hx hp
  rw [abs_of_pos (Real.exp_pos _)]
  exact hx.trans (Real.rpow_le_rpow_of_exponent_le hp.le (by have := le_max_left (-b) (1:ℝ); unfold N; linarith))

lemma monitor_cutoff {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) :
    Rate G L a (fun x => Real.exp (-δ*(Delay.fineMonitor G L x)^γ)) := by
  intro b hb
  let N := max (-b) 1
  have h1 : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_right ..)
  filter_upwards [Fees.hat_decay G L hδ hγ h1,
    (Work.E09.betaF_growth G L).eventually_gt_atTop 1] with x hx hp
  rw [abs_of_pos (Real.exp_pos _)]
  exact hx.trans (Real.rpow_le_rpow_of_exponent_le hp.le (by have := le_max_left (-b) (1:ℝ); unfold N; linarith))

lemma below (h : Rate G L a w) (h₀ : a < 0) : ∀ (c : ℝ), 0 < c → ∀ᶠ x in atTop, |w x| ≤ c := by
  intro c hc
  let b := -a/2
  have hh : 0 < b := by unfold b; linarith
  filter_upwards [Delay.shift_pos G L,h (-b) (by unfold b; linarith),
    ((tendsto_rpow_atTop hh).comp (Work.E09.betaF_growth G L)).eventually_ge_atTop c⁻¹]
    with x hx he hI
  apply he.trans
  rw [Real.rpow_neg hx.le]; change c⁻¹ ≤ betaF G x L^b at hI
  exact (inv_anti₀ (inv_pos.mpr hc) hI).trans_eq (inv_inv c)
end Rate
end YM.ConnectedActivityE6
