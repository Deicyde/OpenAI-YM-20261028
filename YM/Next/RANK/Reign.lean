import Mathlib.Analysis.ODE.ExistUnique
import YM.Analysis.Polydisc
import YM.Euclid.Comparator
import YM.Next.RANK.Value
import YM.PCalc.Band

/-!
# Numeric prices: p scale, restored radii and weights

Use a threshold-function overload to keep post-L expenses visible in the test
on actual clock. Uniform window hats $u\in[s/2,s]$; prove this Hertz bound
separately when using same fixed L height. No uniform claim before choosing L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Perch
open Function Set Filter Asymptotics Real RG RG.Supply Vac Lattice 
open scoped Topology BigOperators Classical

-- keep parentheses on logs!

def y (s : ℝ) := Real.log (Real.log s)
def boil (s : ℝ) := (y s)^2 -- log p(s), nonnegative
lemma boil_pos (s : ℝ) : 0 ≤ boil s := sq_nonneg _
def bill (a s : ℝ) := Real.exp (boil s * a)

def M (s : ℝ) := Nat.ceil ((Real.log s) ^2)
def walls (s : ℝ) := (M s)^2

def hot (s : ℝ) := Real.exp ((y s)^ ((3:ℝ)/2))
def join (s : ℝ) := (hot s)^((1:ℝ)/5)
def w (s : ℝ) := Real.exp (- (7/10) * join s)
lemma strong (s : ℝ) : w s≤1 := Real.exp_le_one_iff.mpr (by unfold join hot; apply mul_nonpos_of_nonpos_of_nonneg (by norm_num); positivity)

theorem y_rate : Tendsto y atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
theorem boil_rate : Tendsto boil atTop atTop := (tendsto_pow_atTop (n:=2) (by norm_num)).comp y_rate
lemma bill_lo {a : ℝ} (h : 0<a) : Tendsto (bill a) atTop atTop := Real.tendsto_exp_atTop.comp (boil_rate.atTop_mul_const h)
lemma bill_hi {a : ℝ} (h : a<0) : Tendsto (bill a) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp
  ( (tendsto_neg_atBot_iff.mpr boil_rate).atBot_mul_const (neg_pos.mpr h) |>.congr (fun _ => neg_mul_neg .. |>.trans rfl))
lemma overlap (a b s : ℝ) : bill a s * bill b s=bill (a+b) s := by simp [bill,mul_add,Real.exp_add]

lemma wall_mono : MonotoneOn walls (Ici 1) := fun _ hi _ _ he => pow_le_pow_left' (Nat.ceil_le_ceil
  (pow_le_pow_left₀ (Real.log_nonneg hi) (Real.log_le_log (zero_lt_one.trans_le hi) he) 2)) _
theorem many : Tendsto M atTop atTop := tendsto_nat_ceil_atTop.comp ((tendsto_pow_atTop (n:=2) (by norm_num)).comp Real.tendsto_log_atTop)
lemma big : Tendsto walls atTop atTop := (tendsto_pow_atTop (n:=2) (by norm_num)).comp many

lemma hot_mono {s u : ℝ} (hs : Real.exp 1 ≤ s) (he : s≤u) : hot s ≤ hot u := by
  have hp := (Real.exp_pos _).trans_le hs
  have hf : 1≤Real.log s := by rw [Real.le_log_iff_exp_le hp]; exact hs
  exact Real.exp_le_exp.mpr (Real.rpow_le_rpow (Real.log_nonneg hf) (Real.log_le_log (zero_lt_one.trans_le hf) (Real.log_le_log hp he)) (by norm_num))
lemma join_mono {s u : ℝ} (hs : Real.exp 1 ≤ s) (he : s≤u) : join s ≤ join u :=
  Real.rpow_le_rpow (Real.exp_pos _).le (hot_mono hs he) (by norm_num)
lemma surge : Tendsto hot atTop atTop := Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num : 0 < (3:ℝ)/2)).comp y_rate)
lemma up : Tendsto join atTop atTop := (tendsto_rpow_atTop (by norm_num : 0 < (1:ℝ)/5)).comp surge

lemma half : Tendsto (fun s : ℝ => s/2) atTop atTop := tendsto_id.atTop_div_const (by norm_num : 0 < (2:ℝ))

/-- $y(s) ≤ y(s/2)+1$ eventually. -/
lemma logspan : ∀ᶠ s in atTop, y s ≤ y (s/2)+1 := by
  filter_upwards [(Real.tendsto_log_atTop.comp half).eventually_ge_atTop (max 1 (Real.log 2)),eventually_gt_atTop 0] with s hs hp
  have hf := (le_max_left ..).trans hs; change 1 ≤ Real.log (s/2) at hf
  have he : Real.log 2 ≤ Real.log (s/2) := (le_max_right ..).trans hs
  have hz : Real.log s = Real.log (s/2)+Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by norm_num),div_mul_cancel₀]; norm_num
  have hp' : 0 < Real.log (s/2) := zero_lt_one.trans_le hf
  have ht : (2:ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have hY : 0 < Real.log s := hz.symm ▸ by linarith only [hp',Real.log_pos (show 1<(2:ℝ) by norm_num)]
  unfold y; apply (Real.log_le_iff_le_exp hY).2
  rw [Real.exp_add,Real.exp_log hp']; linarith only [hz,he,mul_le_mul_of_nonneg_left ht hp'.le]

lemma rate_wall {a : ℝ} (ha : 0<a) (c : ℝ) : ∀ᶠ s in atTop, c*Real.log (walls s:ℝ) ≤ a*boil s := by
  -- M=ceil exp(2*y), walls=M^2
  have hM : ∀ᶠ s in atTop, Real.log (walls s:ℝ) ≤ 6*y s := by
    filter_upwards [y_rate.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1] with s hs hh
    have hx : 1≤Real.log s := hh; have he : Real.log s = Real.exp (y s) := (Real.exp_log (zero_lt_one.trans_le hx)).symm
    have hu : (M s:ℝ) < (Real.log s)^2+1 := Nat.ceil_lt_add_one (sq_nonneg _)
    have ht : (Real.log s)^2=Real.exp (2*y s) := by rw [he,two_mul,Real.exp_add,pow_two]
    have hy : 1 ≤ Real.exp (2*y s) := Real.one_le_exp (by linarith)
    have hv : 2 ≤ Real.exp (y s) := by linarith only [Real.add_one_le_exp (y s),hs]
    have hp : (M s:ℝ) ≤ Real.exp (3*y s) := by rw [show 3*y s=2*y s+y s by ring,Real.exp_add]; linarith only [ht,hu,hy,mul_le_mul_of_nonneg_left hv (Real.exp_pos (2*y s)).le]
    have hh : (0:ℝ) < M s := by exact_mod_cast (Nat.ceil_pos.mpr (by positivity : 0 < Real.log s ^ 2))
    unfold walls; rw [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat]
    linarith only [(Real.log_le_iff_le_exp hh).mpr hp]
  rcases le_or_gt c 0 with h|h
  · filter_upwards [big.eventually_ge_atTop 1] with s hs
    exact (mul_nonpos_of_nonpos_of_nonneg h (Real.log_nonneg (by exact_mod_cast hs))).trans (mul_nonneg ha.le (boil_pos _))
  filter_upwards [hM,y_rate.eventually_ge_atTop (6*c/a)] with s hs hy
  have he : 6*c ≤ y s*a := (div_le_iff₀ ha).mp hy
  have hv : 0≤ y s := le_trans (by positivity) hy
  unfold boil; linarith only [mul_le_mul_of_nonneg_left hs h.le,mul_le_mul_of_nonneg_left he hv]


-- tolerate restored cost exp(c log p) in forced hit and pack exponent
lemma rate_inverse (a : ℝ) (ha : 0<a) : ∀ᶠ s in atTop, boil s ≤ a*↑(walls (s/2)) := by
  have ht := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2 |>.comp (y_rate.comp half)
  filter_upwards [ht.eventually (ge_mem_nhds (by linarith : 0 < a/4)),y_rate.eventually_ge_atTop 1,
    (y_rate.comp half).eventually_ge_atTop 1,logspan,(Real.tendsto_log_atTop.comp half).eventually_ge_atTop 1] with s hs he hz hv hu
  let y' := y (s/2)
  change y'^2*Real.exp (-y') ≤ a/4 at hs; change 1≤y' at hz; change 1≤Real.log (s/2) at hu
  have hp : y s ≤ y'+1 := hv
  have hh : y s ^ 2 ≤ 4*y'^2 := by nlinarith
  have hm : Real.exp y' ≤ M (s/2) := by
    unfold y' y;
    rw [Real.exp_log (by linarith)]; exact le_trans (by nlinarith) (Nat.le_ceil ((Real.log (s/2))^2))
  have hc : 1 ≤ (M (s/2):ℝ) := (Real.one_le_exp (by linarith)).trans hm
  have hy : Real.exp y' ≤ ((walls (s/2)):ℝ) := by unfold walls; push_cast; exact le_trans hm (by nlinarith)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)] at hs
  unfold boil; linarith only [mul_le_mul_of_nonneg_left hy ha.le,hh,hs]

lemma rate_fire (a : ℝ) (ha : 0<a) : ∀ᶠ s in atTop, boil s ≤ a*join (s/2) := by
  -- eventually Join(s/2) beats exp(y')
  have h (z : ℝ) (hz : 25 ≤ z) : z ≤ z^((3:ℝ)/2)/5 := by
    rw [show (3:ℝ)/2=1+(1/(2:ℝ)) by ring,Real.rpow_add (by linarith), Real.rpow_one,← Real.sqrt_eq_rpow]
    have he : 5 ≤ Real.sqrt z := Real.le_sqrt_of_sq_le (by linarith); linarith only [mul_le_mul_of_nonneg_left he (show 0 ≤ z by linarith)]
  filter_upwards [((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp (y_rate.comp half)).eventually (ge_mem_nhds (by linarith : 0 < a/4)),
    y_rate.eventually_ge_atTop 1,(y_rate.comp half).eventually_ge_atTop 25, logspan] with s hs he ht hh
  let z := y (s/2)
  change z^2*Real.exp (-z) ≤ a/4 at hs; change 25 ≤ z at ht
  have hp : Real.exp z ≤ join (s/2) := by unfold join hot; rw [← Real.exp_mul,one_div,← div_eq_mul_inv]; exact Real.exp_le_exp.mpr (h z ht)
  rw [Real.exp_neg,← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)] at hs
  have hx : boil s ≤ 4*z^2 := by change y s^2 ≤ _; change y s≤z+1 at hh; nlinarith
  linarith only [hs,hx,mul_le_mul_of_nonneg_left hp ha.le]

-- Even in comparing different inputs throughout the entire H stretch.
private lemma fire_compare (s : ℝ) : join s= Real.exp ((y s)^((3:ℝ)/2)/5) := by unfold join hot; rw [← Real.exp_mul,one_div, ← div_eq_mul_inv]

lemma fire_stretch : ∀ᶠ s in atTop, join s ≤ hot (s/2) := by
  filter_upwards [logspan,(y_rate.comp half).eventually_ge_atTop 1,y_rate.eventually_ge_atTop 1] with s hs hv hz
  let z := y (s/2); change 1≤z at hv; change y s ≤ z+1 at hs
  have hh : y s ≤ 2*z := by linarith
  have he : (y s)^((3:ℝ)/2)≤ (2*z)^((3:ℝ)/2) := Real.rpow_le_rpow (by linarith) hh (by norm_num)
  have hm : (2:ℝ)^((3:ℝ)/2) ≤ (5:ℝ) := by
    have h1 := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) (by norm_num : (3:ℝ)/2 ≤ 2)
    norm_num at h1; exact le_trans h1 (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at he
  rw [fire_compare,hot]; apply Real.exp_le_exp.mpr
  change y s ^ ((3:ℝ)/2) / 5 ≤ z ^ _; linarith only [he,mul_le_mul_of_nonneg_right hm (show 0 ≤ z^((3:ℝ)/2) by positivity)]
end YM.Next.Rank.Perch
