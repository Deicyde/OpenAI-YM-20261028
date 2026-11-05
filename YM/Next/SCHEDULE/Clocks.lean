import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Analysis.Polydisc
import YM.Bid.Fuels
import YM.Work.A05.Read
import YM.Work.A07

/-!
# Entrance arithmetic at fixed L

`x` is hat beta (β̂), not an actual coupling. All assertions here at
individual fixed stage (before choosing progression to higher stages). Pay a
numerical accuracy threshold at that stage to get smallness through the
subsequently built hierarchy. No uniform claim made by taking this limit.
Use `watch 2` for ordinary p, `watch (3/2)` for restarted threshold sizes.
Separate lower/upper tail estimates for support and forced activities. Powers
can be chosen after L when NOT incurred repeatedly. Coordination with the
pre-L bills in later modules.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Clock
open Filter Function Asymptotics Real
open scoped Topology

def tick (x : ℝ) := log (log x)

def cover (x : ℝ) := Nat.ceil (log x^ (2:ℕ))

def gap (x : ℝ) := (√x)⁻¹

def watch (d x : ℝ) := exp (tick x ^ d)

lemma wp (d x) : 0 < watch d x := exp_pos _
lemma watch_two (x) : watch 2 x = exp (tick x ^ (2:ℕ)) := by norm_num [watch,rpow_two]
lemma gp {x} (h : 0 < x) : 0 < gap x := inv_pos.mpr (Real.sqrt_pos.2 h)

lemma clock : Tendsto tick atTop atTop := tendsto_log_atTop.comp tendsto_log_atTop
lemma growing {d} (hd : 0 < d) : Tendsto (watch d) atTop atTop :=
  tendsto_exp_atTop.comp ((tendsto_rpow_atTop hd).comp clock)

lemma counting : Tendsto cover atTop atTop := by
  unfold cover
  have h := (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp tendsto_log_atTop
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [h.eventually_ge_atTop (b:ℝ)] with x hx
  exact_mod_cast (le_trans (show (b:ℝ) ≤ (log x)^ (2:ℕ) from hx) (Nat.le_ceil _))

lemma log_tick {x : ℝ} (h : 1 < x) : exp (tick x) = log x := exp_log (log_pos h)
lemma log_gap {x : ℝ} (h : 0 < x) : log (gap x)=-(1/2:ℝ)*log x := by rw [gap, log_inv, log_sqrt h.le]; ring
lemma formula {x : ℝ} (h : 1 < x) : gap x=exp (-exp (tick x)/2) := by
  rw [log_tick h,show -log x/2= log (gap x) by rw [log_gap (by linarith)]; ring,
    exp_log (gp (by linarith))]
lemma cover_lo {x : ℝ} (h : 1 < x) : exp (2*tick x) ≤ (cover x:ℝ) := by
  rw [two_mul,Real.exp_add,log_tick h]; unfold cover; rw [← sq]; exact Nat.le_ceil _
lemma cover_hi {x : ℝ} (h : exp 1 ≤ x) : 1+(cover x:ℝ) ≤ exp (log 3+2*tick x) := by
  have hx : 1 < x := (one_lt_exp_iff.2 zero_lt_one).trans_le h
  have he : 1 ≤ log x := by rw [le_log_iff_exp_le (by linarith)]; exact h
  have hu := (Nat.ceil_lt_add_one (sq_nonneg (log x))).le
  rw [exp_add,exp_log (by norm_num : (0:ℝ)<3), two_mul,exp_add,log_tick hx]
  unfold cover; nlinarith

/-- Use ratio-to-zero to pay an exponentially bigger test quantity. -/
lemma negative {f g : ℝ → ℝ} {c : ℝ} (hg : Tendsto g atTop atTop)
    (h : f =o[atTop] g) (hc : 0 < c) : Tendsto (fun x => f x-c*g x) atTop atBot := by
  refine tendsto_atBot.mpr fun b => ?_
  filter_upwards [h.def (half_pos hc), hg.eventually (eventually_gt_atTop (0:ℝ)),
    hg.eventually (eventually_ge_atTop (-b/(c/2)))] with x hx hy ht
  have hr : f x ≤ c/2*g x := by
    rw [norm_of_nonneg hy.le] at hx
    exact (le_norm_self _).trans hx
  have hz := (div_le_iff₀ (half_pos hc)).1 ht; linarith

private lemma linear_bot (d a b c : ℝ) (hd : 1 < d) (hc : 0 < c) :
    Tendsto (fun y : ℝ => a+b*y-c*y^d) atTop atBot := by
  have ht := tendsto_rpow_atTop (show 0<d by linarith)
  refine negative ht ?_ hc
  have h : (fun y : ℝ => y) =o[atTop] (fun y => y^d) := by
    refine isLittleO_iff.2 fun c hc => ?_
    have hD : Tendsto (fun y : ℝ => c * y^(d-1)) atTop atTop :=
      Tendsto.const_mul_atTop hc (tendsto_rpow_atTop (by linarith))
    filter_upwards [eventually_gt_atTop (0:ℝ),hD.eventually_ge_atTop 1] with x hx hA
    have he := mul_le_mul_of_nonneg_right (show 1 ≤ c*x^(d-1) from hA) hx.le
    have hh : c*x^(d-1)*x=c*x^d := by rw [Real.rpow_sub hx,Real.rpow_one]; field_simp
    rw [norm_of_nonneg hx.le,norm_of_nonneg (Real.rpow_pos_of_pos hx _).le]; linarith
  exact ((isLittleO_const_id_atTop a).trans h).add (h.const_mul_left b)

/-- watch-powers negligible against arbitrary inverse gap powers (at x→∞,
fixed d, a). -/
lemma light (d p a : ℝ) (ha : 0 < a) :
    Tendsto (fun x => watch d x ^ p * gap x ^ a) atTop (𝓝 0) := by
  have hm : Tendsto (fun y : ℝ => p*y^d-(a/2)*exp y) atTop atBot :=
    negative tendsto_exp_atTop ((isLittleO_rpow_exp_atTop _).const_mul_left p) (half_pos ha)
  refine ((Real.tendsto_exp_atBot.comp hm).comp clock).congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  dsimp only [Function.comp_apply,watch]; rw [formula hx,← Real.exp_mul,← Real.exp_mul,← exp_add]; ring_nf

lemma checks_gauge : Tendsto gap atTop (𝓝 0) := by simpa using light 2 0 1 (by norm_num)

lemma ceiling_cheaper (d a : ℝ) (k : ℕ) (hd : 1 < d) (ha : 0 < a) :
    Tendsto (fun x => (1+(cover x:ℝ))^k/(watch d x ^ a)) atTop (𝓝 0) := by
  let F (y : ℝ) := log 3*k+(2:ℝ)*k*y-a*y^d
  have hF : Tendsto F atTop atBot := linear_bot _ _ _ _ hd ha
  apply squeeze_zero' (g:=fun x => exp (F (tick x))) _ _ ((tendsto_exp_atBot.comp hF).comp clock)
  · filter_upwards with x
    have := wp d x; positivity
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  apply le_trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) (cover_hi hx) k) (Real.rpow_pos_of_pos (wp d x) _).le)
  unfold F watch
  rw [← Real.exp_nat_mul, ← exp_mul, ← exp_sub]; apply le_of_eq; congr 1; ring

/-- `1/ĝ^D` absorbed by *support* exponential. Note w^-1 NOT
billed here. `p` arbitrary real. -/
lemma shadows (p c : ℝ) (hc : 0 < c) :
    Tendsto (fun x => gap x ^ p * exp (-c*(cover x:ℝ))) atTop (𝓝 0) := by
  have he : Tendsto (fun y : ℝ => -(p/2)*exp y-c*exp (2*y)) atTop atBot := by
    refine negative ?_ ?_ hc
    · exact tendsto_exp_atTop.comp (Tendsto.const_mul_atTop (by norm_num) tendsto_id)
    refine IsLittleO.const_mul_left ?_ _
    rw [Real.isLittleO_exp_comp_exp_comp]
    simpa only [two_mul, add_sub_cancel_right] using! (tendsto_id (x:=(atTop:Filter ℝ)))
  apply squeeze_zero' _ _ ((tendsto_exp_atBot.comp he).comp clock)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have := gp hx; positivity
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  dsimp only [comp_apply]; rw [formula hx, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_monotone
  nlinarith only [hc,cover_lo hx]

/-- Inverse gap powers absorbed also by gas weights. -/
lemma burnt (p c d a : ℝ) (hc : 0 < c) (hd : 1 < d) (ha : 0 < a) :
    Tendsto (fun x => gap x ^ p * exp (-c * watch d x ^ a)) atTop (𝓝 0) := by
  have ht := tendsto_exp_atTop.comp (Tendsto.const_mul_atTop ha (tendsto_rpow_atTop (y := d) (by linarith)))
  have h : (fun y : ℝ => exp y) =o[atTop] (fun y => exp (a*y^d)) := by
    rw [Real.isLittleO_exp_comp_exp_comp]
    -- from linear_bot
    have hb := linear_bot d 0 1 a hd ha
    simpa [Function.comp_def] using! tendsto_neg_atBot_atTop.comp hb
  have he := negative ht (h.const_mul_left (-(p/2))) hc
  refine ((tendsto_exp_atBot.comp he).comp clock).congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  dsimp only [Function.comp_apply,watch]; rw [formula hx,← Real.exp_mul,← Real.exp_mul,← exp_add]; ring_nf

/-- Pay inverse gas weights THIS way, from the strong reserve; period and
copy-count absent from the constants. -/
lemma incinerate (p c d b : ℝ) (k : ℕ) (hc : 0 < c) (hd : 1 < d) :
    Tendsto (fun x => gap x ^ p *
      exp (-c * watch d x ^ (2:ℕ) / (1+(cover x:ℝ))^k+b*watch d x ^ ((1:ℝ)/5))) atTop (𝓝 0) := by
  have h := burnt p (c/2) d 1 (half_pos hc) hd zero_lt_one
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have := gp hx; positivity
  have hl := growing (d:=d) (by linarith)
  have hh : Tendsto (fun w : ℝ => b/w^(1-(1:ℝ)/5)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num))
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (ceiling_cheaper d 1 k hd zero_lt_one).eventually (ge_mem_nhds zero_lt_one),
    (hh.comp hl).eventually (ge_mem_nhds (half_pos hc))] with x hx hn hm
  let W := watch d x; have hw : 0 < W := wp _ _
  change _ / W^(1:ℝ) ≤ 1 at hn; rw [Real.rpow_one] at hn
  change b/W^(1-(1:ℝ)/5) ≤ c/2 at hm
  rw [Real.rpow_sub hw, Real.rpow_one, div_div_eq_mul_div] at hm
  change _*exp _ ≤ _*exp (_ * W^(1:ℝ))
  refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (Real.rpow_pos_of_pos (gp hx) _).le
  rw [Real.rpow_one]
  let v := (1+(cover x:ℝ))^k; have hv : 0 < v := by unfold v; positivity
  have hi : v ≤ W := by simpa using (div_le_iff₀ hw).1 hn
  have hb : b*W^((1:ℝ)/5) ≤ c/2*W := (div_le_iff₀ hw).1 hm
  have he : -c * W ^ (2:ℕ) / v ≤ -c * W := by
    refine (div_le_iff₀ hv).2 ?_
    have he := mul_le_mul_of_nonneg_left hi (mul_nonneg hc.le hw.le)
    linarith
  change -c*W^ (2:ℕ)/v+b*W^((1:ℝ)/5) ≤ _
  linarith
end YM.Next.Scheduling.Clock
