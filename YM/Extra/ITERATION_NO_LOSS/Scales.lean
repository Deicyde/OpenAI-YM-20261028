import YM.Extra.ITERATION_NO_LOSS.Post

/-!
# Fixed-stage subpower and reserve comparisons (post L)

Coarse HAT beta x, fine HAT x+a for a fixed shift. No period in these
constants/filters. The faster reserve, not the exp(-c B) reserve, absorbs
arbitrary fixed powers of forced inverse radii.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Scales
open Filter Function Lattice Wilson RG Pressure
open scoped Topology BigOperators

def Tiny (g f : ℝ → ℝ) := ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, 0 ≤ f x ∧ f x ≤ g x ^ ε

namespace Tiny
variable {f g h : ℝ → ℝ}

lemma const (hg : Tendsto g atTop atTop) (c : ℝ) (hc : 0 ≤ c) : Tiny g (fun _ => c) := fun _ he =>
  (((tendsto_rpow_atTop he).comp hg).eventually_ge_atTop c).mono fun _ h => ⟨hc,h⟩
lemma mul (hf : Tiny g f) (hh : Tiny g h) (hg : Tendsto g atTop atTop) : Tiny g (fun x => f x * h x) := by
  intro ε he; have e := half_pos he
  filter_upwards [hf _ e,hh _ e,hg.eventually (eventually_gt_atTop 0)] with x hx hy hz
  exact ⟨mul_nonneg hx.1 hy.1, (mul_le_mul_of_nonneg hx.2 hy.2 hx.1 (hy.1.trans hy.2)).trans_eq (by rw [← Real.rpow_add hz,add_halves])⟩
lemma add (hf : Tiny g f) (hh : Tiny g h) (hg : Tendsto g atTop atTop) : Tiny g (fun x => f x + h x) := by
  intro ε he; have e := half_pos he
  filter_upwards [hf _ e,hh _ e,Tiny.const hg 2 (by norm_num) _ e,hg.eventually (eventually_gt_atTop 0)] with x hx hy h2 hz
  refine ⟨add_nonneg hx.1 hy.1,(add_le_add hx.2 hy.2).trans ?_⟩
  rw [← two_mul]; exact (mul_le_mul_of_nonneg_right h2.2 (Real.rpow_nonneg hz.le _)).trans_eq (by rw [← Real.rpow_add hz,add_halves])
lemma pow (hf : Tiny g f) (hg : Tendsto g atTop atTop) (k : ℕ) : Tiny g (fun x => f x ^ k) := by
  induction k with
  | zero => simpa using Tiny.const hg 1 zero_le_one
  | succ k ih => simpa only [pow_succ] using ih.mul hf hg

/-- Against the shifted monitor. No `log 0` in this use. -/
lemma logarithmic (a : ℝ) : Tiny (fun x => meter (x+a)) Real.log := by
  intro ε he
  filter_upwards [(loop_ratio a ε).eventually (le_mem_nhds (show (1/2:ℝ)<1 by norm_num)), eventually_ge_atTop (2:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (2/ε),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (Real.log 2)] with x hh hx hB hL
  let y := Real.log (Real.log x)
  have hY : 2 ≤ y * ε := (div_le_iff₀ he).mp hB
  have h0 : Real.log 2 ≤ y := hL
  have hp : 0 < Real.log x := Real.log_pos (by linarith)
  refine ⟨hp.le, le_trans ?_ ((le_div_iff₀ (Real.rpow_pos_of_pos (meter_pos _) _)).mp hh)⟩
  have hz : 2 * Real.log x ≤ meter x ^ ε := by
    rw [meter, Vac.Numbers.P, Real.rpow_def_of_pos (Real.exp_pos _) _, Real.log_exp, show (2:ℝ)*Real.log x = Real.exp (Real.log 2+y) by
      rw [Real.exp_add,Real.exp_log hp,Real.exp_log (by norm_num : 0<(2:ℝ))]]
    change Real.exp _ ≤ Real.exp (y^2*ε); apply Real.exp_monotone; nlinarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
  linarith

lemma grow (a : ℝ) : Tendsto (fun x => meter (x+a)) atTop atTop := meter_grows.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
lemma cover (a : ℝ) : Tiny (fun x => meter (x+a)) (fun x => (1+(radiusB x:ℝ))) := by
  have h := (Tiny.const (grow a) 2 (by norm_num)).add ((logarithmic a).pow (grow a) 2) (grow a)
  intro ε he; filter_upwards [h ε he] with x hx
  exact ⟨by positivity,le_trans (by unfold radiusB; linarith only [(Nat.ceil_lt_add_one (sq_nonneg (Real.log x))).le] : 1+(radiusB x:ℝ) ≤ 2+(Real.log x)^2) hx.2⟩
lemma meter_pow (a b : ℝ) : Tiny id (fun x => meter (x+a)^b) := by
  intro ε he; have h : Tendsto (fun x : ℝ => x+a) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hx := Tiny.const tendsto_id (2^(ε/2):ℝ) (by positivity) _ (half_pos he)
  filter_upwards [h.eventually (Vac.Numbers.cost b _ (half_pos he)),eventually_gt_atTop (0:ℝ),h.eventually (eventually_ge_atTop (0:ℝ)),eventually_ge_atTop a,hx]
    with x h hx hz ha hE
  refine ⟨Real.rpow_nonneg (meter_pos _).le _, h.trans ?_⟩
  calc
    _ ≤ (2*x)^(ε/2) := Real.rpow_le_rpow hz (by linarith) (by linarith)
    _ ≤ x^ε := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hx.le]
      apply (mul_le_mul_of_nonneg_right (show _ ≤ x^(ε/2) from hE.2) (show 0 ≤ x^(ε/2) by positivity)).trans_eq
      rw [← Real.rpow_add hx, add_halves]
lemma cover_size : Tiny id (fun x => (1+(radiusB x:ℝ))) := by
  intro ε he; filter_upwards [cover 0 1 zero_lt_one,meter_pow 0 1 ε he] with x hx hy
  rw [Real.rpow_one] at hx; rw [Real.rpow_one] at hy
  exact ⟨hx.1,hx.2.trans hy.2⟩
end Tiny

lemma first (c s : ℝ) (hc : 0<c) : ∀ᶠ x : ℝ in atTop, Real.exp (-c * radiusB x) ≤ x^(-s) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (s / c),eventually_gt_atTop (1:ℝ)] with x hx hy
  rw [Real.rpow_def_of_pos (by linarith : 0<x)]
  have h := (div_le_iff₀ hc).mp hx
  have hz : (Real.log x)^2 ≤ (radiusB x:ℝ) := Nat.le_ceil _
  exact Real.exp_monotone (by nlinarith [Real.log_pos hy])

/-- `w^{-1}` and arbitrary beta powers paid simultaneously by the second
reserve; can include arbitrary coefficients of either sign. -/
lemma second (a c s b d : ℝ) (hc : 0 < c) (n : ℕ) : ∀ᶠ x : ℝ in atTop,
    Real.exp (b*meter x^((1:ℝ)/5) + d*meter (x+a)^((1:ℝ)/5)) *
      Real.exp (-c*meter (x+a)^ (2:ℕ) / (1+(radiusB x:ℝ))^n) ≤ x^(-s) := by
  have he := (loop_ratio a ((1:ℝ)/5)).eventually (le_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  filter_upwards [he,Tiny.logarithmic a 1 zero_lt_one, (Tiny.pow (Tiny.cover a) (Tiny.grow a) n) (1/2) (by norm_num),
    ((tendsto_rpow_atTop (y:=(1/2:ℝ)) (by norm_num)).comp (Tiny.grow a)).eventually_ge_atTop ((2*|b|+|d|+|s|)/c),eventually_gt_atTop (1:ℝ)]
    with x he hlog hB hq hx
  let p := meter (x+a); let y := p ^ (1/2:ℝ)
  have hp : 1 ≤ p := meter_ge _
  have h : (1+ (radiusB x:ℝ))^n ≤ y := hB.2
  rw [Real.rpow_one] at hlog
  have hlog : Real.log x ≤ p := hlog.2
  have he' := (le_div_iff₀ (Real.rpow_pos_of_pos (meter_pos x) ((1:ℝ)/5))).mp he
  have hl : p^((1:ℝ)/5) ≤ p := (Real.rpow_le_rpow_of_exponent_le hp (by norm_num : (1:ℝ)/5 ≤ 1)).trans_eq (Real.rpow_one _)
  have hv : y^ (2:ℕ) = p := by unfold y; rw [← Real.rpow_mul_natCast (by linarith)]; norm_num
  change 1/2*meter x^((1:ℝ)/5) ≤ p^((1:ℝ)/5) at he'
  have he'' := (div_le_iff₀ hc).mp hq
  rw [← Real.exp_add, Real.rpow_def_of_pos (by linarith : 0<x)]
  refine Real.exp_monotone ?_
  have ht : b*meter x^((1:ℝ)/5) + d*p^((1:ℝ)/5) + s*Real.log x ≤ (2*|b|+|d|+|s|)*p := by
    have hw := Real.rpow_nonneg (meter_pos x).le ((1:ℝ)/5)
    linarith [mul_le_mul (le_abs_self b) (show meter x ^ ((1:ℝ)/5) ≤ 2 * p by linarith) hw (abs_nonneg b),
      mul_le_mul (le_abs_self d) hl (Real.rpow_nonneg (by linarith : 0 ≤ p) ((1:ℝ)/5)) (abs_nonneg d),
      mul_le_mul (le_abs_self s) hlog (Real.log_nonneg hx.le) (abs_nonneg s)]
  change _ + -c*p^ (2:ℕ) / _ ≤ _
  have hh := mul_le_mul he'' h (by positivity) (by unfold y; positivity : 0 ≤ y*c)
  have hf : (2*|b|+|d|+|s|)*p ≤ c*p^(2:ℕ)/(1+(radiusB x:ℝ))^n := by
    apply (le_div_iff₀ (by positivity)).mpr
    change _ ≤ y*c*y at hh; rw [mul_right_comm,← sq,hv] at hh
    nlinarith
  rw [neg_mul,neg_div]; linarith
end YM.Extra.Iteration.Scales
