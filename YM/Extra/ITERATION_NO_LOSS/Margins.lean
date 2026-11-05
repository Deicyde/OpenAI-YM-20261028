import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Extra.ITERATION_NO_LOSS.Scales

/-!
# Reserve the E,K and |ε_kin| margins in coarse-HAT variables

Band uniform. Our displayed weak bill uses one common post-L nonnegative
integer power for simplicity. θ at the input index fixed for this comparison.
`b` is actual fine beta. No estimate on an activity assumed inside these
numeric implications. Strong forced bill separate (must have been obtained
with the required p_*² rate).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Scales
open Filter Function Lattice Wilson RG Pressure Vac.Numbers
open scoped Topology BigOperators

local notation "g" => Hat

def unforced (x : ℝ) := Hat x ^ ((11:ℝ)/5)
def forced (x : ℝ) := Real.exp (-(meter x ^ ((1:ℝ)/5)))
def stock (y θ : ℝ) := 2*meter y ^ θ

def poly (C : ℝ) (k : ℕ) (x y θ : ℝ) := C * (1+(radiusB x:ℝ) + meter y + stock y θ)^k
def seeds (c : ℝ) (k : ℕ) (x y : ℝ) := Real.exp (-c*radiusB x) + Real.exp (-c*meter y^ (2:ℕ)/(1+(radiusB x:ℝ))^k)
def bill (C c : ℝ) (k : ℕ) (x y θ b : ℝ) := poly C k x y θ * (Hat b^3 + (Hat b)⁻¹^k * seeds c k x y)
def marked (C c y b : ℝ) := C * Real.exp (-c * (temp y / Hat b)^ (2:ℕ))

lemma tiny_poly (a C θ : ℝ) (hC : 0 ≤ C) (k : ℕ) : Tiny id (fun x => poly C k x (x+a) θ) := by
  have hm := Tiny.meter_pow a 1; simp_rw [Real.rpow_one] at hm
  have h := (Tiny.cover_size.add hm tendsto_id).add ((Tiny.const tendsto_id 2 (by norm_num)).mul (Tiny.meter_pow a θ) tendsto_id) tendsto_id
  exact (Tiny.const tendsto_id C hC).mul (h.pow tendsto_id k) tendsto_id

lemma hat_price (x b : ℝ) (hx : 0 < x) : g x ^ b = x ^ (-(1/2:ℝ)*b) := by rw [Real.rpow_mul hx.le, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]; rfl
lemma hat_cube (x : ℝ) (hx : 0 < x) : g x ^ (3 : ℕ) = x ^ (-(3/2:ℝ)) := by
  rw [← Real.rpow_natCast, hat_price _ _ hx]; norm_num
lemma loan {f : ℝ → ℝ} (h : Tiny id f) : ∀ᶠ x : ℝ in atTop, f x * g x ^ (3:ℕ) ≤ unforced x := by
  filter_upwards [eventually_gt_atTop (1:ℝ), h (1/4) (by norm_num)] with x hx hh
  have hy := zero_lt_one.trans hx
  calc
    _ ≤ (x ^ (1/4:ℝ)) * x ^ (-(3/2:ℝ)) := by rw [hat_cube x hy]; exact mul_le_mul_of_nonneg_right hh.2 (by positivity)
    _ ≤ _ := by rw [← Real.rpow_add hy,unforced,hat_price _ _ hy]; exact Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)

lemma pay_seeds (a c : ℝ) (k : ℕ) (hc : 0<c) : ∀ᶠ x : ℝ in atTop, ∀ b : ℝ, (x+a)/2 ≤ b → b ≤ 2*(x+a) →
    g b ^ (3:ℕ) + ((g b)⁻¹)^k * seeds c k x (x+a) ≤ 10*g x ^ (3:ℕ) := by
  have he := second a c (k+2) 0 0 hc k
  filter_upwards [he,first c (k+2) hc,eventually_gt_atTop (8:ℝ),eventually_ge_atTop a,eventually_ge_atTop (-2*a)] with x hs hf hx ha ha' b hb hb'
  have hp : 0 < b := by linarith
  have hy : 0 < x := by linarith
  have hsb := Real.sqrt_pos.mpr hp; have hsx := Real.sqrt_pos.mpr hy
  have hz := Real.sqrt_le_iff.mpr (show 0 ≤ x ∧ b ≤ x^2 by constructor <;> nlinarith)
  have hg : Hat b ≤ 2*g x := by
    unfold Hat
    rw [← one_div, le_mul_inv_iff₀ hsx,one_div_mul_eq_div,div_le_iff₀ hsb]
    nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hy.le]
  have hs' : seeds c k x (x+a) ≤ x^(-(k+2:ℝ)) + x^(-(k+2:ℝ)) := add_le_add hf (by simpa using hs)
  have hk : x ^ (-(2:ℝ)) ≤ Hat x ^ (3:ℕ) := by rw [hat_cube x hy]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [show (Hat b)⁻¹ = Real.sqrt b from inv_inv ..]
  calc
    _ ≤ (2*g x)^(3:ℕ) + x^k * (x^(-(k+2:ℝ)) + x^(-(k+2:ℝ))) :=
      add_le_add (pow_le_pow_left₀ (by unfold Hat; positivity) hg _) (mul_le_mul (pow_le_pow_left₀ hsb.le hz k) hs' (by unfold seeds; positivity) (by positivity))
    _ ≤ _ := by rw [← Real.rpow_natCast x k, mul_add, ← Real.rpow_add hy, show (k:ℝ) + -(k+2:ℝ) = -2 by ring]; linarith

lemma pay_regular (C A c a θ : ℝ) (k : ℕ) (hC : 0 < C) (hA : 0 ≤ A) (hc : 0<c) : ∀ᶠ x : ℝ in atTop,
    poly A k x (x+a) θ * temp x ^ (3:ℕ) ≤ unforced x / 8 ∧ ∀ b : ℝ, (x+a)/2 ≤ b → b ≤ 2*(x+a) →
      C*bill A c k x (x+a) θ b ≤ unforced x / 8 := by
  have h := tiny_poly a A θ hA k; have hm := Tiny.meter_pow 0 3
  have h3 : Tiny id (fun x => meter x^ (3:ℕ)) := by
    convert hm using 2 with x; simp only [add_zero]; exact (Real.rpow_natCast _ 3).symm
  filter_upwards [pay_seeds a c k hc, loan ((Tiny.const tendsto_id (8*10*C) (by positivity)).mul h tendsto_id),
    loan (((Tiny.const tendsto_id 8 (by norm_num)).mul h tendsto_id).mul h3 tendsto_id)] with x hx h1 h2
  constructor
  · change _ * (g x * meter x)^3 ≤ _; rw [mul_pow]; linarith
  intro b hb hb'; have hA : 0 ≤ poly A k x (x+a) θ := by unfold poly stock; have := meter_pos (x+a); positivity
  unfold bill; linarith only [h1,mul_le_mul_of_nonneg_left (hx b hb hb') (mul_nonneg hC.le hA)]

lemma unforced_mono {x y : ℝ} (hx : 0 < x) (hy : x ≤ y) : unforced y ≤ unforced x := by
  rw [unforced,unforced,hat_price _ _ hx, hat_price _ _ (hx.trans_le hy)]
  exact Real.rpow_le_rpow_of_nonpos hx hy (by norm_num)
lemma unforced_threshold {x : ℝ} (hx : 1 < x) : unforced x ≤ temp x ^ (2:ℕ) := by
  have hy := zero_lt_one.trans hx
  calc
    _ ≤ x^(-(1:ℝ)) := by rw [unforced,hat_price _ _ hy]; exact Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
    _ = g x ^ (2:ℕ) := by rw [← Real.rpow_natCast,hat_price _ _ hy]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by unfold Hat; positivity) (le_mul_of_one_le_right (by unfold Hat; positivity) (meter_ge x)) _

lemma pay_forced (a C c γ : ℝ) (hc : 0<c) (hg : 0 < γ) (hcg : γ ≤ c/4) : ∀ᶠ x : ℝ in atTop,
    Real.exp (-γ * meter (x+a)^ (2:ℕ)) ≤ forced x ∧ ∀ b : ℝ, (x+a)/2 ≤ b → marked C c (x+a) b ≤ Real.exp (-γ * meter (x+a)^ (2:ℕ)) := by
  have h := ((tendsto_pow_atTop (n:=2) (by decide)).comp (Tiny.grow a)).const_mul_atTop (show 0<c/2-γ by linarith)
  filter_upwards [(Real.tendsto_exp_atTop.comp h).eventually_ge_atTop C, eventually_gt_atTop (-a),
    (Tiny.grow a).eventually_ge_atTop (2/γ), (loop_ratio a 1).eventually (le_mem_nhds (show (1/2:ℝ)<1 by norm_num))] with x hC' hx hm hx'
  let p := meter (x+a); let y := x+a; have hy : 0 < y := by dsimp [y]; linarith
  have hp : 1 ≤ p := meter_ge y
  constructor
  · apply Real.exp_monotone
    simp only [Real.rpow_one] at hx'
    have he := (le_div_iff₀ (meter_pos _)).mp hx'
    have ht : meter x ^ ((1:ℝ)/5) ≤ meter x := (Real.rpow_le_rpow_of_exponent_le (meter_ge x) (by norm_num : (1:ℝ)/5 ≤ 1)).trans_eq (Real.rpow_one _)
    change -γ * p ^ (2:ℕ) ≤ _
    have hm : 2 ≤ p * γ := (div_le_iff₀ hg).mp hm
    change _ ≤ p at he; nlinarith
  intro b hb; have hb' : 0 < b := by change y/2≤b at hb; linarith
  have hh : p^ (2:ℕ)/2 ≤ (temp y/g b)^ (2:ℕ) := by
    change p^ (2:ℕ)/2 ≤ ((Real.sqrt y)⁻¹*p/(Real.sqrt b)⁻¹)^ (2:ℕ)
    rw [div_pow,mul_pow,inv_pow, inv_pow,Real.sq_sqrt hy.le,Real.sq_sqrt hb'.le]; field_simp; change y/2 ≤ b at hb; nlinarith
  have hC' : C ≤ Real.exp ((c/2-γ)*p^(2:ℕ)) := hC'
  calc
    _ ≤ Real.exp ((c/2-γ)*p^ (2:ℕ))*Real.exp (-c*(temp y/g b)^2) := mul_le_mul_of_nonneg_right hC' (Real.exp_pos _).le
    _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_monotone; change _ ≤ -γ*p^ (2:ℕ); nlinarith
end YM.Extra.Iteration.Scales
