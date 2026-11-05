import YM.Ac.Table
import YM.Bid.Drops
import YM.Next.SCHEDULE.Clocks
import YM.Org.Theatre

/-!
# Entrance arithmetic: uniform neighboring hat-beta levels

Stronger than needed to choose fixed-L *one-step* adjacent references: look all
the way up and down within √x of x, suitable for sublinear comparison work
stretches (actual h budget charged separately). Pay even the displayed
`exp (-P^(1/5))`-ratio, through an UNBOUNDED number of such close levels
(pairwise comparison, don't multiply any per-step ratio). d parameters here
include both ordinary and restarted weak monitor conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Clock
open Filter Function Asymptotics Real Set
open scoped Topology

def near (x a : ℝ) := |x-a| ≤ √x

lemma same (x : ℝ) : near x x := by simp only [near,sub_self,abs_zero]; exact Real.sqrt_nonneg _

lemma away {x a : ℝ} (hx : 4 ≤ x) (h : near x a) : x/2 ≤ a := by
  obtain ⟨-,h⟩:= abs_le.mp h
  nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (by linarith : 0 ≤ x)]

lemma advance {P : ℝ → Prop} (he : ∀ᶠ x in atTop, P x) : ∀ᶠ x in atTop, ∀ a, near x a → P a := by
  obtain ⟨B,hB⟩:=eventually_atTop.1 he
  filter_upwards [eventually_ge_atTop (2*B),eventually_ge_atTop (4:ℝ)] with x hX hx
  exact fun a ha => hB a (le_trans (by linarith) (away hx ha))

def Lags (f : ℝ → ℝ) := ∀ ε : ℝ, 0<ε → ∀ᶠ x in atTop, ∀ a b, near x a → near x b → |f a - f b| ≤ ε

lemma mean {f f' : ℝ → ℝ} (h : ∀ᶠ x : ℝ in atTop, HasDerivAt f (f' x) x)
    (hp : Tendsto (fun x : ℝ => f' x*√x) atTop (𝓝 0)) : Lags f := by
  intro ε hε
  have he := hp.norm.eventually (ge_mem_nhds (show ‖(0:ℝ)‖ < ε/4 by simp [hε]))
  filter_upwards [eventually_ge_atTop (4:ℝ),advance (he.and h)] with x hx hF
  intro a b ha hb
  have ht : 0 < x := by linarith
  have hX : 0 < √x := Real.sqrt_pos.2 ht
  let I := Icc (x-√x) (x+√x)
  have hi (u : ℝ) : u∈I ↔ near x u := by simp only [I,mem_Icc,near,abs_le]; constructor <;> rintro ⟨h,h'⟩ <;> constructor <;> linarith
  have hz (u) (hu : u∈I) : ‖f' u‖ ≤ ε/(2*√x) := by
    have hk := away hx ((hi u).mp hu)
    have hh := (hF u ((hi u).mp hu)).1
    simp only [norm_mul,norm_of_nonneg (Real.sqrt_nonneg _)] at hh
    have hy : √x ≤ 2*√u := by
      have := Real.sqrt_nonneg u; nlinarith [Real.sq_sqrt ht.le, Real.sq_sqrt (by linarith : 0 ≤ u)]
    apply (le_div_iff₀ (by positivity)).mpr
    have hr := mul_le_mul_of_nonneg_left hy (norm_nonneg (f' u))
    linarith
  have hR := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun u hu => (hF u ((hi u).1 hu)).2.hasDerivWithinAt)
    hz (convex_Icc ..) ((hi b).2 hb) ((hi a).2 ha)
  simp only [Real.norm_eq_abs] at hR
  apply hR.trans
  have hh : |a-b| ≤ 2*√x := by
    obtain ⟨h,h'⟩:=abs_le.mp ha
    obtain ⟨hx,hx'⟩:=abs_le.mp hb
    apply abs_le.mpr; constructor <;> linarith
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = ε := by field_simp

lemma root_identity {x : ℝ} (h : 0 < x) : x⁻¹*√x=gap x := by
  unfold gap
  have he : 0 < √x := Real.sqrt_pos.2 h
  field_simp; nlinarith [Real.sq_sqrt h.le]

lemma lags_log : Lags log := by
  apply mean (f':=fun x => x⁻¹)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx using Real.hasDerivAt_log hx.ne'
  apply checks_gauge.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx using (root_identity hx).symm

lemma Lags.scale {f : ℝ → ℝ} (h : Lags f) (p : ℝ) : Lags (fun x => p*f x) := by
  intro ε hε; filter_upwards [h (ε/(|p|+1)) (by positivity)] with x hx
  intro a b ha hb; have hz := hx a b ha hb
  have ht := (le_div_iff₀ (by positivity)).1 hz
  rw [← mul_sub,abs_mul]; linarith [abs_nonneg (f a-f b)]

lemma Lags.fixes {f g : ℝ → ℝ} (h : Lags f) (he : f =ᶠ[atTop] g) : Lags g := by
  intro ε hε; filter_upwards [h ε hε,advance he] with x hx he a b ha hb
  rw [← he a ha, ← he b hb]; exact hx a b ha hb

private def tickDeriv (d x : ℝ) := d * tick x ^ (d-1)*(log x)⁻¹*x⁻¹
private lemma deriv_tick (d : ℝ) : ∀ᶠ x : ℝ in atTop, HasDerivAt (fun x => tick x^d) (tickDeriv d x) x := by
  filter_upwards [eventually_gt_atTop (exp 1),clock.eventually (eventually_gt_atTop (0:ℝ))] with x hx h1
  have ht : 1 < x := (one_lt_exp_iff.2 zero_lt_one).trans hx
  have h := HasDerivAt.rpow_const (p:=d) (HasDerivAt.log (Real.hasDerivAt_log (show x≠0 by linarith)) (log_pos ht).ne')
    (Or.inl (ne_of_gt (show 0<tick x from h1)))
  convert h using 1 <;> simp only [tickDeriv,tick]
  ring

private lemma tick_rate (d : ℝ) : Tendsto (fun x : ℝ => tick x^(d-1)*(log x)⁻¹) atTop (𝓝 0) := by
  have hl := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d-1) 1 zero_lt_one
  refine (hl.comp clock).congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx; dsimp only [comp_apply]
  rw [neg_mul,one_mul,exp_neg,log_tick hx]

lemma lags_tick (d : ℝ) : Lags (fun x => tick x^d) := by
  apply mean (deriv_tick d)
  have ht : Tendsto (fun x : ℝ => d*(tick x^(d-1)*(log x)⁻¹)*gap x) atTop (𝓝 0) := by
    simpa using (((tick_rate d).const_mul d).mul checks_gauge)
  apply ht.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  unfold tickDeriv; rw [← root_identity hx]; ring

lemma lags_watch (d p : ℝ) : Lags (fun x => watch d x^p) := by
  let f (x : ℝ) := exp (p*tick x^d)
  have he : (fun x => watch d x^p)=f := by ext x; unfold f watch; rw [← exp_mul,mul_comm p]
  rw [he]
  apply mean (f':=fun x => f x*p*tickDeriv d x)
  · filter_upwards [deriv_tick d] with x hx
    convert (hx.const_mul p).exp using 1; unfold f; ring
  have hx : Tendsto (fun x => f x*gap x) atTop (𝓝 0) := by
    rw [← he]; simpa using light d p 1 (by norm_num)
  have ht : Tendsto (fun x => (f x*gap x)*p*d*(tick x^(d-1)*(log x)⁻¹)) atTop (𝓝 0) := by
    simpa using (((hx.mul_const _).mul_const _).mul (tick_rate d))
  apply ht.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  unfold tickDeriv; rw [← root_identity hx]; ring

def Similar (f : ℝ → ℝ) := ∀ θ : ℝ, 1<θ → ∀ᶠ x in atTop, ∀ a b, near x a → near x b → f a ≤ θ*f b

lemma Lags.affords {f : ℝ → ℝ} (h : Lags (fun x => log (f x))) (hp : ∀ᶠ x in atTop,0 < f x) : Similar f := by
  intro θ hθ
  filter_upwards [h _ (log_pos hθ),advance hp] with x hx hm a b ha hb
  apply (Real.log_le_log_iff (hm a ha) (mul_pos (by linarith) (hm b hb))).mp
  rw [Real.log_mul (by linarith) (hm b hb).ne']
  have := (abs_le.mp (hx a b ha hb)).2; linarith

lemma similar_gap_power (a : ℝ) : Similar (fun x => gap x ^ a) := by
  apply Lags.affords
  · refine (lags_log.scale (-(a/2))).fixes ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [log_rpow (gp hx),log_gap hx]; ring
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx using Real.rpow_pos_of_pos (gp hx) _

lemma similar_watch_power (d p : ℝ) : Similar (fun x => watch d x ^ p) := by
  apply Lags.affords
  · simpa only [watch, ← exp_mul, log_exp,mul_comm p] using (lags_tick d).scale p
  exact Eventually.of_forall fun x => Real.rpow_pos_of_pos (wp d x) _

lemma similar_gas (d p u : ℝ) : Similar (fun x => exp (-u * watch d x ^ p)) := by
  apply Lags.affords _ (Eventually.of_forall fun x => exp_pos _)
  simpa only [log_exp] using (lags_watch d p).scale (-u)

lemma similar_log_sq : Similar (fun x => log x^ (2:ℕ)) := by
  apply Lags.affords
  · simpa [tick] using (lags_tick 1).scale 2
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx using pow_pos (log_pos hx) _

lemma similar_cover : Similar (fun x => (cover x:ℝ)) := by
  intro θ hθ
  let c := (1+θ)/2
  have hh : 1 < c := by unfold c; linarith
  have ht : 0 < θ-c := by unfold c; linarith
  have hm := (Tendsto.const_mul_atTop ht ((tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp tendsto_log_atTop))
  filter_upwards [similar_log_sq c hh,advance (hm.eventually_ge_atTop 1)] with x hx hp a b ha hb
  have he : log a^ (2:ℕ) ≤ c*log b^ (2:ℕ) := hx a b ha hb
  have hu : 1 ≤ (θ-c)*log b^ (2:ℕ) := hp b hb
  apply le_trans _ (mul_le_mul_of_nonneg_left (Nat.le_ceil (log b^ (2:ℕ))) (by linarith))
  exact le_trans (Nat.ceil_lt_add_one (sq_nonneg _)).le (by linarith)
end YM.Next.Scheduling.Clock
