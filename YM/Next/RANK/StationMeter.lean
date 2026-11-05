import YM.Cells.Corrected
import YM.Next.RANK.Determinant
import YM.Next.RANK.Station

/-!
# How large is a station bill?

Don't prescribe the relative smallness of L against the next stage here.
Freeze a charge for the whole stage before doing a radius estimate. The
output per-cell cost loses a harmonic log correction, not a per-site log loss.
We show it can use 1 after going to deeper cells, **uniformly even on the
smallest period**. Stage-dependent costs here must be paid by an explicit
scale delay; an argument with `constant in that window` but no such bound would
not suffice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Station
open Asymptotics Filter Function Set Lattice Wilson RG Real Extraction Cells
open scoped Topology BigOperators

variable {G : Gauge}

/-- Terminal vacuum parameters eligible for (this version of) the price.
All mask tests made at the given threshold. Permit larger coupling range &
changed thresholds on the ancillary run. The equality of densities &
β-on-course is required separately. -/
structure Meets (A : Levels G) (m p : ℕ) (P : Rep G (A.S.side m p)) (g Λ δ : ℝ) : Prop where
  same : P.clip=(A.params m).clip
  cap : P.beta ≤ 4*A.clock.hatBeta m
  assigned : P.beta*g^2=1
  positive : 0<g
  entrance : g ≤ P.p.threshold
  max_threshold : P.p.threshold ≤ A.clock.threshold m
  cap_E : δ ≤ 1
  loopCap : Λ ≤ A.clock.loopCap m

variable (O : HaarBudget G) (A : Levels G)

-- determinant per-site stage gate, includes unit overhead. R,m explicit.
def ticket (O : HaarBudget G) (s : Stage) (m : ℕ) : ℝ :=
  2*(1+(8*s.paths+1)) + Fintype.card PlaqAxes +
    (Fintype.card PlaqAxes:ℝ)*(s.clip.direct+s.paths^2)/2 + (1+(m:ℝ)) +
      3*ent O s.clip - 4*Real.log O.small + 1

private lemma rolls_law (h : G.Simple) : ∀ᶠ m : ℕ in atTop, ∀ p (P : Rep G (A.S.side m p)) (g Λ δ X : ℝ) (k : ℕ),
    Meets A m p P g Λ δ → X ≤ 1+k → protection O P (A.params m).paths Λ δ X g ≤ ticket O (A.params m) k - 1 := by
  filter_upwards [(hat_rate A h).eventually YM.Vac.Numbers.uniform_loop] with m hm
  let a := A.params m
  let b := A.clock.hatBeta m
  let t := A.clock.threshold m
  rintro p P g Λ δ X k H he
  have hl : A.clock.loopCap m * t^2 ≤ 1 := by
    refine hm.2.2.2 _ ((A.fits.thetaRange m).2.trans ?_)
    have hy : (1:ℝ) ≤ A.clock.J m := by have ht := A.clock.adm m; exact_mod_cast (by omega : 1 ≤ A.clock.J m)
    exact le_trans (inv_anti₀ zero_lt_one hy) inv_one.le
  have ht : 0<P.p.threshold := P.p.threshold_pos
  have hY : Λ*P.p.threshold^2 ≤ 1 := by
    have hx : 0 ≤ A.clock.loopCap m := by unfold Calendar.loopCap Calendar.monitor; positivity
    apply le_trans ?_ hl; exact mul_le_mul H.loopCap (pow_le_pow_left₀ ht.le H.max_threshold _) (sq_nonneg _) hx
  have hf := H.assigned
  let r := a.paths
  have hR : 0 < r := a.paths_pos
  have hE : P.exCost r Λ δ ≤ 1+(8*r+1) := by
    have h3 : b*t^3 ≤ 1 := hm.2.1
    have h4 : b*t^4 ≤ 1 := hm.2.2.1
    apply add_le_add H.cap_E (add_le_add _ hY)
    have hc := H.cap
    have hy : 0 < b := zero_lt_one.trans (A.fits.delayed m)
    apply (mul_le_mul hc (add_le_add (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ht.le H.max_threshold 3) hR.le) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le H.max_threshold 4) hR.le))
      (show 0 ≤ r*P.p.threshold^3+r*P.p.threshold^4 by positivity) (show 0 ≤ 4*b by positivity)).trans
    change 4*b*(r*t^3+r*t^4) ≤ 8*r; linarith only [mul_le_mul_of_nonneg_left h3 hR.le, mul_le_mul_of_nonneg_left h4 hR.le]
  have hb : P.beta*baseBudget P.clip r g=(Fintype.card PlaqAxes:ℝ)*(P.clip.direct+r^2)/2 := by
    unfold baseBudget; linear_combination (Fintype.card PlaqAxes:ℝ)*(P.clip.direct+r^2)/2*hf
  unfold protection ticket
  change 2*P.exCost r Λ δ+_+P.beta*baseBudget P.clip r g+_+_-_ ≤ _
  rw [hb,H.same]; change P.exCost (A.params m).paths Λ δ ≤ _ at hE
  linarith only [hE,he]

private lemma exp_bills (a : ℝ) :
    ∀ᶠ m : ℕ in atTop, a*A.clock.hatBeta m ≤ Real.exp (A.S.scale m) := by
  have hv : (fun s : ℝ => a*(A.clock.bar+G.slopeConstant*s)) =o[atTop] Real.exp := by
    have hh (n : ℕ) : (fun x : ℝ => x^n) =o[atTop] Real.exp := by simpa using isLittleO_pow_exp_pos_mul_atTop n (zero_lt_one' ℝ)
    have hx : _ := ((hh 0).const_mul_left A.clock.bar).add ((hh 1).const_mul_left G.slopeConstant)
    simpa using! (hx.const_mul_left a)
  have he := (hv.comp_tendsto A.S.divergent).def zero_lt_one
  filter_upwards [he] with m hm
  refine le_trans (le_abs_self _) ?_
  simpa only [Calendar.hatBeta, Function.comp_def, one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using! hm

private lemma four_prices : ∀ᶠ m : ℕ in atTop, ∀ p (P : Rep G (A.S.side m p)) (g Λ δ : ℝ),
    Meets A m p P g Λ δ → -(4:ℝ)*G.lieDim*Real.log g/(Fintype.card (Site (A.S.side m p)):ℝ) ≤ 1 := by
  filter_upwards [exp_bills A (8*G.lieDim)] with m hm p P g Λ δ H
  rw [div_le_one (by exact_mod_cast (Fintype.card_pos (α:=Site (A.S.side m p))))]
  set d := G.lieDim
  have he : P.beta=(1 / g^2) := (eq_div_iff (pow_ne_zero _ H.positive.ne')).2 H.assigned
  have hb : 0<P.beta := he ▸ div_pos zero_lt_one (pow_pos H.positive _)
  have hh : -(4:ℝ) * G.lieDim * Real.log g=2*d*Real.log P.beta := by rw [he,one_div,Real.log_inv,Real.log_pow];unfold d; ring
  rw [show -(4:ℝ)*d*Real.log g= _ from hh]
  let v := A.S.denominator m
  let N := A.S.side m p
  calc
    _ ≤ (8*d)*A.clock.hatBeta m := by
      have hk := mul_le_mul_of_nonneg_left ((Real.log_le_self hb.le).trans H.cap) (show 0 ≤ (2:ℝ)*d by positivity)
      linarith only [hk]
    _ ≤ _ := hm
    _ ≤ _ := by
      rw [Schedule.scale,Schedule.a,inv_inv,Real.exp_log (by positivity)]
      rw [site_card]
      have hv : v.val ≤ N.val := Nat.le_mul_of_pos_left _ (A.S.period p).property
      have hN : 1 ≤ N.val := N.property
      have hh : N.val ≤ N.val^4 := by simpa only [pow_one] using (pow_le_pow_right₀ hN (by norm_num : 1 ≤ 4))
      exact_mod_cast hv.trans hh

/-- Price of determinant at all sufficiently fine widths (uniform periods).
Arity per cell enters additively *before* this bound. Does not produce any
`Notice` or `Meets`. -/
theorem affordable (h : G.Simple) : ∀ᶠ m : ℕ in atTop, ∀ p (P : Rep G (A.S.side m p)) (g Λ δ X : ℝ) (k : ℕ),
    Meets A m p P g Λ δ → X ≤ 1+k → protection O P (A.params m).paths Λ δ X g - 4*G.lieDim*Real.log g/(Fintype.card (Site (A.S.side m p)):ℝ) ≤ ticket O (A.params m) k := by
  filter_upwards [rolls_law O A h,four_prices A] with m hm hp
  intro p P g Λ δ X k H he; have hl := hp _ _ _ _ _ H
  simp only [neg_mul,neg_div] at hl; linarith only [hm _ _ _ _ _ _ _ H he,hl]
end YM.Next.Rank.Station
