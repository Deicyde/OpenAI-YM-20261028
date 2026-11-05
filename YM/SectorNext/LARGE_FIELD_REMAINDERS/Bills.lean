import YM.SectorNext.LARGE_FIELD_REMAINDERS.Marginal
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Multiplier



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Paying the hole and analytic bills in the grant's quantifier order

Includes reserve for extra priced losses per seed (to use with other
multiplier, K, support payments). Here at scale b=(1+B); e.g. absorb
arbitrary fixed $C_L(1+B)^4(1+\\log\\beta)$ in the exponent per seed.
And delayed *bulk* per-site price for the remaining oriented cut and
reweighting at a stated cap. These are bounds on exponential density
parts at physical normalization, not logs of the partition.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Metric Oriented Presented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ENNReal

variable (G : Gauge) (L : Side)

/-- Hatted currency actually earned per share, without the kernel's Z. Beta
on the input/fine band. -/
def seed (x κ β : ℝ) (m : ℕ) := β*(κ*(fiery G x L)^2*m)
lemma earned {x κ β : ℝ} {m : ℕ} (h : 0<y G L x) (hκ : 0 ≤ κ) (hβ : y G L x/2 ≤ β) :
    (κ/2*(p G L x)^2*m) ≤ seed G L x κ β m := by
  have hh : 0≤κ*(fiery G x L)^2*m := by positivity
  apply le_trans ?_ (mul_le_mul_of_nonneg_right hβ hh)
  rw [fi,mul_pow]
  refine le_of_eq ?_
  calc
    _ = κ/2*p G L x^2*m*(y G L x*g G L x^2) := by rw [yg2 G L h]; ring
    _ = _ := by ring

lemma s_le {x : ℝ} (h : 1 < y G L x) (m : Mode) : g G L x ≤ m.size G L x := by
  cases m
  · rw [Mode.size,fi]; apply le_mul_of_one_le_right (Scales.gauge G L (zero_lt_one.trans h)).le
    unfold p; rw [Next.Scheduling.Clock.watch_two]; exact Real.one_le_exp (sq_nonneg _)
  rfl

lemma g01 {x : ℝ} (h : 1 < y G L x) : 0<g G L x ∧ g G L x < 1 := by
  have he : 0 < y G L x := zero_lt_one.trans h
  refine ⟨Scales.gauge G L he,?_⟩
  unfold g Next.Scheduling.Clock.gap
  have hk := Real.sq_sqrt he.le; have hh := Real.sqrt_pos.2 he
  rw [inv_lt_one₀ hh]; nlinarith

def haloCost (L : Side) (x : ℝ) := (L.val:ℝ)^4 * Fintype.card Axis * 4 * 9^4 * (b x)^4

def coin (H : ℝ) (n : ℕ) (x : ℝ) := H * (b x)^n * (1 + Real.log (y G L x))

/-- Halo ownership and other priced spends on packet interiors & boundaries,
including comparing at fluctuation scale even at inactive positions. Spend
κ/2 (in actual fine β currency), or any other strictly positive budget.
Doesn't claim later Mayer m-volume estimates have this price. -/
theorem hole_price (κ H : ℝ) (n : ℕ) (hk : 0<κ) (hH : 0≤H) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {c f : Side} (S : StepData c f), S.patch.L=L → ∀ (A : Stores S) (F : Forest S.ratio) (m : Mode) (β : ℝ),
      y G L x/2 ≤ β → Real.exp (coin G L H n x * A.shares) * hole F A G x (m.size G L x) ≤
        Real.exp (seed G L x κ β A.shares / 2) := by
  let D := (dim G:ℝ)
  let a : ℝ := (L.val:ℝ)^4*Fintype.card Axis*4*9^4
  have ha : 0≤a := by unfold a; positivity
  let f x := 1+Real.log (y G L x)
  have hh : Tendsto (fun x => (coin G L H n x +haloCost L x*D*f x)/(p G L x)^ (2:ℕ)) atTop (𝓝 0) := by
    have ht := ((inactive_price G L n (a:=2) (by norm_num)).const_mul H).add
      ((inactive_price G L 4 (a:=2) (by norm_num)).const_mul (a*D))
    simp only [mul_zero,add_zero,Real.rpow_two] at ht
    exact ht.congr fun x => by dsimp only [Function.comp_apply, coin,haloCost,f,a,D]; ring
  filter_upwards [(year G L).eventually_gt_atTop 1, hh.eventually (ge_mem_nhds (show 0<κ/4 by positivity))] with x he hx
  intro c f' S hl A F m β hβ
  have hy := (g01 G L he).1
  have hf : 0≤f x := by unfold f; have := Real.log_nonneg he.le; positivity
  have hb : 0 ≤ b x := by linarith [size x]
  let cnt := (frozen A (radiusB x) F).card
  have hcount : (cnt:ℝ) ≤ haloCost L x * A.shares := by
    have hi := frozen_card A (radiusB x) F; rw [hl] at hi
    apply le_trans (Nat.cast_le (α:=ℝ).mpr hi)
    push_cast; unfold haloCost
    have he : 8*(radiusB x:ℝ)+1 ≤ 9*b x := by unfold b; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
    have hh : _ ≤ (9*b x)^4 := pow_le_pow_left₀ (by positivity) he 4
    rw [mul_pow] at hh
    rw [mul_assoc ((L.val:ℝ)^4*(Fintype.card Axis:ℝ)*4) (9^4)]
    gcongr _ * ?_ * _
  let p := p G L x
  have hc := (div_le_iff₀ (show 0 < p^ (2:ℕ) by unfold p; have := Scales.pos G L x; positivity)).mp hx
  have hg : (g G L x)⁻¹ ≤ Real.exp (f x) := by
    unfold g Next.Scheduling.Clock.gap; rw [inv_inv]; unfold f; rw [Real.exp_add,Real.exp_log (by linarith)]
    have hi := Real.one_le_exp (show (0:ℝ)≤1 by norm_num)
    have hr := Real.sqrt_pos.mpr (show 0<y G L x by linarith)
    have hw := Real.sq_sqrt (show 0≤y G L x by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hi (show 0≤y G L x by linarith)]
  have hw := earned G L (zero_lt_one.trans he) hk.le (m:=A.shares) hβ
  let t := m.size G L x
  have ht := s_le G L he m
  have hsize : 0 < t := hy.trans_le ht
  have hD : 0≤D := by unfold D; positivity
  unfold hole
  calc
    _ ≤ Real.exp (coin G L H n x * A.shares) * ((Real.exp (f x)) ^ dim G)^cnt := by
      have hf : t⁻¹ ≤ Real.exp (f x) := (inv_anti₀ hy ht).trans hg
      apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact pow_le_pow_left₀ (pow_nonneg (inv_nonneg.mpr hsize.le) _) (pow_le_pow_left₀ (inv_nonneg.mpr hsize.le) hf _) _
    _ = Real.exp (coin G L H n x * A.shares+(cnt:ℝ)*(D*f x)) := by rw [Real.exp_add (coin G L H n x * A.shares),Real.exp_nat_mul]; rw [show Real.exp (D*f x) = _ from Real.exp_nat_mul (f x) (dim G)]
    _ ≤ _ := by
      apply Real.exp_monotone
      change κ/2*p^2* (A.shares:ℝ) ≤ _ at hw
      have he' := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (α:=ℝ) A.shares)
      have hx' := mul_le_mul_of_nonneg_right hcount (mul_nonneg hD hf)
      linarith only [he',hx',hw]

variable {n : Side}

/-- Bills for base-tail and loop/additive reweighting and exterior loss.
Use only with the stated price caps including the threshold in the same normalization.
One per site combined (or could be made 1+ε for δ=1). Factor L^4 not needed on
coarse rows because already paying even per FINE site. -/
theorem bulk_price (σ C : ℝ) {error : ℝ → ℝ} (he : Tendsto (fun x => y G L x * error x) atTop (𝓝 0))
    (hσ : 0 < σ) (hC : 0 < C) : ∀ᶠ x in atTop, ∀ n : Side, ∀ (R : Rep G n) (δ Λ : ℝ),
      δ ≤ 1 → Λ ≤ 2*p G L x → R.p.threshold = fiery G x L →
      R.beta ∈ Set.Icc (y G L x/2) (2*y G L x) → 0≤error x →
      air R x σ C Λ δ + R.beta*error x ≤ 2 := by
  let u : ℝ := Fintype.card PlaqAxes
  have hu : 0≤u := Nat.cast_nonneg _
  let g := g G L; let p := p G L; let t x := fiery G x L
  have h n : Tendsto (fun x => p x^n * g x) atTop (𝓝 0) := by simpa only [pow_zero,one_mul,p,g] using tally_g G L 0 n
  have hl n : Tendsto (fun x => p x^n * g x^2) atTop (𝓝 0) := by
    have ht := (h n).mul (minute G L); rw [mul_zero] at ht
    exact ht.congr fun x => by unfold g; ring
  let tail x := Real.exp (-σ*(till x))
  have ht : Tendsto (fun x => y G L x * tail x) atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul,tail] using cutoff G L 0 0 hσ
  have hb n (x : ℝ) (hp : 0 < y G L x) :
      y G L x * (t x)^(n+2)=p x^(n+2)*g x^n := by
    unfold t; rw [fi,mul_pow,pow_add (Scales.g G L x) n 2]
    have hh := yg2 G L hp
    calc
      _ = Scales.p G L x^(n+2)*Scales.g G L x^n*(y G L x*Scales.g G L x^2) := by ring
      _ = _ := by rw [hh]; ring
  let F x := 2*C*(p x^3*g x) + 2*C*(p x^4*g x^2) + 2*(p x^3*g x^2) +
    (8*u*C^2)*(y G L x*tail x) + 2*(y G L x*error x)
  have hF : Tendsto F atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (((( (h 3).const_mul (2*C)).add ((hl 4).const_mul (2*C))).add
      ((hl 3).const_mul 2)).add (ht.const_mul (8*u*C^2))).add (he.const_mul 2)
  filter_upwards [(year G L).eventually_gt_atTop 1,hF.eventually (ge_mem_nhds zero_lt_one)] with x hx hY
  intro n R δ Λ hd hΛ hR hβ hz
  have hh := zero_lt_one.trans hx
  have hR3 : y G L x * (t x)^3=p x^3*g x := by simpa using hb 1 x hh
  have hR4 : y G L x * (t x)^4=p x^4*g x^2 := hb 2 x hh
  have hRp : p x *(t x)^2 = p x^3*g x^2 := by unfold t p g; rw [fi]; ring
  have hs : 0≤t x := (Work.E09.temp_pos hh).le
  have ha : 0≤tail x := (Real.exp_pos _).le
  unfold air PathData.loopsPrice; rw [hR]
  change δ+(R.beta*(C*(t x)^3+C*(t x)^4)+Λ*(t x)^2) + R.beta*u*(4*C^2*tail x)+_ ≤ _
  dsimp only [F] at hY
  have h1 := mul_le_mul_of_nonneg_right hβ.2 (show 0≤C*(t x)^3+C*(t x)^4 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hβ.2 (show 0≤u*(4*C^2*tail x) by positivity)
  have h3 := mul_le_mul_of_nonneg_right hΛ (sq_nonneg (t x))
  have h4 := mul_le_mul_of_nonneg_right hβ.2 hz
  change Λ * _ ≤ 2*p x * _ at h3
  linarith only [hd,hY,h1,h2,h3,h4,congrArg (C*·) hR3,congrArg (C*·) hR4,hRp]

end YM.SectorNext.Remainder
