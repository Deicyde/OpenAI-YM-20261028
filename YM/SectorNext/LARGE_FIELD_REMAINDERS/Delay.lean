import YM.Next.EXTRACTION.Tails
import YM.Next.FLUCTUATIONS.Scales
import YM.Next.SCHEDULE.Clocks
import YM.Work.B06



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Delay gains for the sector remainder integrals

At fixed shape/positive rates. Period & input trajectory are not chosen yet.
Mostly consume the verified Clocks gates; x is still coarse-HAT beta while p and g
(and the band) are at shifted beta, with p in *plain* convention. Some jobs only
after L. No power of p charged before a grant is earned, for W/κ calls.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory
   Next.Fluctuations
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical 

variable (G : Gauge) (L : Side)

namespace Scales
open YM.Next.Scheduling.Clock

def y (x : ℝ) := betaF G x L
def g (x : ℝ) := gap (y G L x)
def p (x : ℝ) := watch 2 (y G L x)
def b (x : ℝ) := 1+(radiusB x:ℝ)

lemma year : Tendsto (y G L) atTop atTop := Work.E09.betaF_growth ..
lemma peak : Tendsto (p G L) atTop atTop := (growing two_pos).comp (year G L)
lemma minute : Tendsto (g G L) atTop (𝓝 0) := checks_gauge.comp (year G L)
lemma gauge {x} (hx : 0<y G L x) : 0<g G L x := gp hx
lemma pos (x : ℝ) : 0<p G L x := wp ..
lemma size (x : ℝ) : 1≤b x := by unfold b; simp
lemma fi (x : ℝ) : fiery G x L=g G L x * p G L x := by rw [p, watch_two]; rfl

lemma yg2 {x} (hx : 0<y G L x) : y G L x * g G L x^2=1 := by
  rw [g,gap, inv_pow,Real.sq_sqrt hx.le,mul_inv_cancel₀ hx.ne']

-- Shifted cover size only for pricing.
include G L in
lemma stamp : ∀ᶠ x : ℝ in atTop, b x ≤ 2*(1+(cover (y G L x):ℝ)) := by
  let k : ℝ := G.slopeConstant * Real.log L.val
  filter_upwards [(year G L).eventually (Stock.stepsize (-k))] with x hx
  change radiusB ((x+k)+(-k))^2 ≤ 2*radiusB (y G L x)^2 at hx
  rw [add_neg_cancel_right] at hx
  have he : (radiusB x:ℝ)^2 ≤ 2*(radiusB (y G L x):ℝ)^2 := by exact_mod_cast hx
  unfold b; change _ ≤ 2*(1+(radiusB (y G L x):ℝ))
  nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x),Nat.cast_nonneg (α:=ℝ) (radiusB (y G L x))]

lemma cover_pay (n : ℕ) {a : ℝ} (ha : 0<a) :
    Tendsto (fun x => b x^n / p G L x^a) atTop (𝓝 0) := by
  have hm := ((ceiling_cheaper 2 a n one_lt_two ha).const_mul ((2:ℝ)^n)).comp (year G L)
  rw [mul_zero] at hm
  apply squeeze_zero' (Eventually.of_forall fun x => by have := size x; have := pos G L x; positivity) ?_ hm
  filter_upwards [stamp G L] with x hx
  have h := pos G L x
  dsimp only [Function.comp_apply]
  apply le_trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (show 0≤b x by linarith [size x]) hx n) (Real.rpow_pos_of_pos h _).le)
  rw [mul_pow,p]; exact le_of_eq (by ring)

/-- Only when fixed powers. Does not permit spending, say, c*g*vol when
keeping volume losses bounded across volumes. -/
lemma tally_price (n m : ℕ) {a : ℝ} (ha : 0<a) :
    Tendsto (fun x => b x^n * p G L x^m * (g G L x ^ a)) atTop (𝓝 0) := by
  have he := (cover_pay G L n (show 0<(1:ℝ) by norm_num)).mul ((light 2 (↑(m+1):ℝ) a ha).comp (year G L))
  simp only [mul_zero,Real.rpow_one,Real.rpow_natCast] at he
  refine he.congr (fun x => ?_)
  change b x^n / p G L x * (p G L x^(m+1)*_) = _
  rw [pow_succ]; have hh := (pos G L x).ne'; field_simp; rfl

lemma tally_g (n m : ℕ) : Tendsto (fun x => b x^n * p G L x^m * g G L x) atTop (𝓝 0) := by
  simpa using tally_price G L n m (a:=1) (by norm_num)

lemma tail_price (n m : ℕ) {τ : ℝ} (ht : 0<τ) :
    Tendsto (fun x => b x^n * p G L x^m * Real.exp (-τ*till x)) atTop (𝓝 0) := by
  have he := tally_price G L n m (a:=2) two_pos
  rw [show (fun x => b x ^ n * p G L x ^ m * g G L x ^ (2:ℝ)) = fun x => b x ^ n * p G L x ^ m * g G L x ^ (2:ℕ) by ext x; simp only [Real.rpow_two]] at he
  apply squeeze_zero' ?_ ?_ he
  · filter_upwards with x; have hb := size x; have hp := pos G L x; positivity
  filter_upwards [tail_delay G L _ ht,(year G L).eventually_gt_atTop 0] with x hx hh
  have hb : 0 ≤ b x := by linarith [size x]
  have hp := pos G L x
  have ht' : Real.exp (-τ*till x) ≤ g G L x ^ (2:ℕ) := by
    have hy := yg2 G L hh
    have hv : g G L x^2 = (betaF G x L)⁻¹ := by
      change _ = (y G L x)⁻¹; field_simp; linarith
    rwa [hv]
  exact mul_le_mul_of_nonneg_left ht' (by positivity)

lemma cutoff (n m : ℕ) {τ : ℝ} (ht : 0<τ) :
    Tendsto (fun x => y G L x * (b x^n * p G L x^m * Real.exp (-τ*till x))) atTop (𝓝 0) := by
  let H x := Real.exp (-(τ/2)*till x)
  apply squeeze_zero' (g:=fun x => b x^n * p G L x^m * H x) ?_ ?_ (tail_price G L n m (half_pos ht))
  · filter_upwards [(year G L).eventually_gt_atTop 0] with x hx
    have hb := size x; have hp := pos G L x; positivity
  filter_upwards [tail_delay G L _ (half_pos ht), (year G L).eventually_gt_atTop 0] with x hx hh
  have hb : 0 ≤ b x := by linarith [size x]
  have hp := pos G L x
  have hl : Real.exp (-τ*till x)=H x*H x := by unfold H; rw [← Real.exp_add]; congr 1; ring
  have hy : y G L x * H x ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hx hh.le) (by
    change y G L x * (y G L x)⁻¹ ≤1; rw [mul_inv_cancel₀ hh.ne'])
  calc
    _ = (y G L x * H x) * (b x^n * p G L x^m * H x) := by rw [hl]; ring
    _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (by positivity) (Real.exp_pos _).le) hy

/-- Bill for halo-per-site/polylog loss incurred per seed, when aiming even for
power suppression at the β^-1/2 link scale. Delay after L at *any* rate. -/
lemma inactive_price (n : ℕ) {a : ℝ} (ha : 0<a) :
    Tendsto (fun x => b x^n * (1+Real.log (y G L x)) / p G L x^a) atTop (𝓝 0) := by
  -- Can charge log shift directly to By; buy also By from p(y).
  have he := (cover_pay G L n (half_pos ha)).mul (((ceiling_cheaper 2 (a/2) 1 one_lt_two
    (half_pos ha))).comp (year G L))
  simp only [pow_one,mul_zero] at he
  apply squeeze_zero' ?_ ?_ he
  · filter_upwards [(year G L).eventually_ge_atTop 1] with x hx
    have hp := pos G L x; have hb := size x; have h:=Real.log_nonneg hx; positivity
  filter_upwards [(Real.tendsto_log_atTop.comp (year G L)).eventually_ge_atTop 1] with x hx
  have hb : 0 ≤ b x := by linarith [size x]
  let z := y G L x
  have hx : 1 ≤ Real.log z := hx
  have hm : Real.log z ≤ (cover z:ℝ) := (show Real.log z ≤ (Real.log z)^2 by nlinarith).trans
    (Nat.le_ceil _)
  have hi : p G L x ^ a = p G L x ^ (a/2) * p G L x ^ (a/2) := (by
    rw [← Real.rpow_add (pos G L x),add_halves])
  refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right hm _) (pow_nonneg hb _))
    (Real.rpow_pos_of_pos (pos G L x) _).le).trans ?_
  rw [hi, mul_div_mul_comm]; rfl
end Scales
end YM.SectorNext.Remainder
