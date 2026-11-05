import YM.AnalyticBridge.VERIFIED_RESET_STEP.Trays

/-! All-position fees for the gathering at an output. r*H enters the
regular class with a pre-L multiplier only (no hidden t/radius sizes).
Post-L clipping/hit and higher-order prices explicit. Not paying these
fees just because labels/operations on another prescription were paid. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection
open Function Filter Set Lattice Wilson RG Ovens Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w α Δ : ℝ}
    {X : Listing G n} {v : Source G n}

def turnFee (p : BudgetPoint) := Push.Local.turnCost p.order p.power
lemma turnFee_pos (p : BudgetPoint) : 0 < turnFee p := by unfold turnFee Push.Local.turnCost; positivity

-- unrotated expenses from sums, rotated jets cost turnFee; loosen factor≤1
-- to permit a simpler presentation. These coefficients before multiplies by
-- H are pre-L; α does NOT pay the 2nd order residual part.
def regularNeed (G : Gauge) (p : BudgetPoint) (c : Clip) (σ C α H : ℝ) := resetFee G p*H +
    turnFee p*(H * lowBase G c p σ C + (|α| * p.threshold^3+H)*highBase G p σ C)
def hitPower (p : BudgetPoint) (G : Gauge) (α Δ : ℝ) :=
    |α+Δ| * (2*p.threshold) + |Δ| * (2:ℝ)⁻¹ * pairBill G p * p.threshold^2
def hitNeed (p : BudgetPoint) (G : Gauge) (α H : ℝ) :=
    (|α|+H/p.threshold^2) * (2*p.threshold) + H * (2:ℝ)⁻¹ * pairBill G p
def softNeed (G : Gauge) (p : BudgetPoint) (c : Clip) (σ C α H : ℝ) := softReset G p H + hitNeed p G α H * lowHard p c σ C

lemma budget_pos (p : BudgetPoint) (G : Gauge) (c : Clip) {σ C : ℝ} (hs : 0 < σ) (hc : 0 ≤ C) :
    0 ≤ lowBase G c p σ C ∧ 0 ≤ highBase G p σ C ∧ 0 ≤ lowHard p c σ C := by
  have := lowFee_nonneg G p hs
  have := c.quadratic_pos
  have := both_pos G p hs
  have h : 0 ≤ (1-Real.exp (-(σ/4)))⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
  unfold lowBase highBase lowHard anchoredFee lowerSize Push.AbsoluteSums.Footprint.payment Push.AbsoluteSums.Footprint.degreeIncome
  exact ⟨by positivity, by positivity,by positivity⟩

lemma fresh_allow (hΔ : p.threshold^2 * |Δ| ≤ H) : |α+Δ| * p.threshold^3 ≤ |α| * p.threshold^3 + H := by
  have h := abs_add_le α Δ
  have ht := p.threshold_pos; have hk := p.threshold_le
  linarith only [mul_le_mul_of_nonneg_right h (pow_nonneg ht.le 3),mul_le_mul_of_nonneg_right hk (mul_nonneg (abs_nonneg Δ) (sq_nonneg p.threshold)),hΔ]
lemma hitPower_pos (p : BudgetPoint) (G : Gauge) (α Δ : ℝ) : 0 ≤ hitPower p G α Δ := by
  unfold hitPower; have := pair_nonneg G p; have := p.threshold_pos; positivity
lemma hit_allow (hΔ : p.threshold^2 * |Δ| ≤ H) : hitPower p G α Δ ≤ hitNeed p G α H := by
  have ht := p.threshold_pos; have hk := (le_div_iff₀ (sq_pos_of_pos ht)).mpr ((mul_comm |Δ| _).trans_le hΔ)
  unfold hitPower hitNeed; linarith only [mul_le_mul_of_nonneg_right ((abs_add_le α Δ).trans (add_le_add_right hk _)) (show 0 ≤ 2*p.threshold by linarith),mul_le_mul_of_nonneg_right hΔ (pair_nonneg G p)]

-- Definition includes only *numbers*. Must check all before calling RG.
structure Fees (G : Gauge) (p : BudgetPoint) (c : Clip) (σ C α H w δ γ : ℝ) : Prop where
  regular : regularNeed G p c σ C α H ≤ δ
  hard : ∃ m κ, softNeed G p c σ C α H ≤ m ∧ Payments.Rates p.B γ w m κ

def quoteE (R : PathData G) (p : BudgetPoint) (c : Clip) (α Δ : ℝ) (u : ℕ → ℝ) : EKey n → ℝ := Sum.elim (fun i => resetLoss G p * u i)
    (Sum.elim (fun i => turnFee p * (|Δ| *p.threshold^2) * (|i.2.mark R c| * lowCost G p (i.2.length R)))
      fun i => turnFee p * (|α+Δ| * p.threshold^3) * i.2.price R p)
def quoteL (R : PathData G) (p : BudgetPoint) (c : Clip) (α Δ : ℝ) (u : ℕ → ℝ) : LKey n → ℝ := Sum.elim (fun i => resetLoss G p * u i)
    fun i => hitPower p G α Δ * (Real.exp ((i.2.length R:ℝ)/c.relaxation) * |i.2.mark R c|)
namespace Local
variable (g : G.Simple) (h : Local X p v H w) (hx : R.Bounds c σ C Λ) (hc : Decent c p) (hw : Width p c σ) (α Δ : ℝ)
    {u : ℕ → ℝ}
    (h1 : ∀ i, p.supBounds (X.reg i).site (X.reg i).support (v.logRead i) (u i))
variable (hs : ∀ i, p.Regular (X.reg i).support (v.logRead i))
include g hs h1

include hx hc in
lemma quote_regular (i : EKey n) : p.supBounds (incoming X R p i).site (incoming X R p i).support
    (archive X R c v α Δ i) (quoteE R p c α Δ u i) := by
  rcases i with i|⟨a,d⟩|⟨a,d⟩
  · exact rebate_sup _ g (hs i) (h1 i)
  · refine sup_le (a.sup (d.fresh_regular R c _ hc (factor*Δ)) (Bill.sup (d.fresh_bill R c _ hc _) (fun _ h => h))) ?_
    change turnFee p * (|factor*Δ| * p.threshold^2 * (|d.mark R c| * lowCost G p (d.length R))) ≤
      turnFee p * (|Δ| * p.threshold^2) * (|d.mark R c| * lowCost G p (d.length R))
    rw [mul_assoc (turnFee p),abs_mul,abs_of_pos factor_pos]; gcongr
    · exact turnFee_pos p |>.le
    · exact mul_nonneg (abs_nonneg _) (low_nonneg ..)
    exact mul_le_of_le_one_left (abs_nonneg _) factor_le
  refine sup_le (a.sup (d.fresh_regular R _ hx p (factor*α) (factor*Δ)) (Bill.sup (d.fresh_bill ..) (fun _ he => he))) ?_
  change turnFee p * (|factor*α+factor*Δ| * (d.price R p*p.threshold^3)) ≤ turnFee p * (|α+Δ| * p.threshold^3) * d.price R p
  rw [mul_assoc (turnFee p), mul_assoc, mul_comm (_^3:ℝ),← mul_add,abs_mul, abs_of_pos factor_pos]; gcongr
  · exact turnFee_pos p |>.le
  · exact mul_nonneg (High.price_nn ..) (pow_nonneg p.threshold_pos.le _)
  exact mul_le_of_le_one_left (abs_nonneg _) factor_le

lemma quote_soft (i : LKey n) (U : Config G n) : ‖loses X R c p v α Δ i U‖ ≤ quoteL R p c α Δ u i := by
  rcases i with i|⟨a,d⟩
  · exact fault_sup _ g (hs i) (h1 i) U
  refine (Low.loan_bound R c d 0 p (factor*α) (factor*Δ) _).trans ?_
  change shapeLoss _ _ _ _ _ _ * |d.mark R c| ≤ hitPower p G α Δ * (Real.exp _ * |d.mark R c|)
  rw [shapeLoss, ← mul_assoc (hitPower ..), ← mul_add, abs_mul factor, abs_mul factor, abs_of_pos factor_pos]; unfold hitPower
  have he (x : ℝ) := mul_le_of_le_one_left (abs_nonneg x) factor_le
  have hb := pair_nonneg G p; have hp := p.threshold_pos; gcongr <;> exact he _

include hw hx hc in
omit g hs in
lemma quote_family (hu : Quotes.early p X.reg u H) (hΔ : p.threshold^2* |Δ| ≤ H) :
    anchored p (incoming X R p) (quoteE R p c α Δ u) (regularNeed G p c σ C α H) ∧
      Ac.Hit (soft X R p) p.B (quoteL R p c α Δ u) (p.supportExponent+1) (softNeed G p c σ C α H) := by
  have hC := Cost.nonneg hx.three
  have ⟨he,hk⟩ := enlarging G X.reg hc.radius (fun i => (h1 i).1) hu
  obtain ⟨ha,hb,hl⟩ := rows (n:=n) G R c p hx hw
  obtain ⟨hL,hH,hD⟩ := budget_pos p G c hx.width hC
  have ht := turnFee_pos p
  have hp := p.threshold_pos
  refine ⟨fun o => Cost.enlarge (Cost.sum (he o) (Cost.sum
    (anchored_scale (r:=turnFee p*(|Δ| * p.threshold^2)) (by positivity) ha o)
    (anchored_scale (r:=turnFee p*(|α+Δ| * p.threshold^3)) (by positivity) hb o))) ?_, fun x => ?_⟩
  · unfold regularNeed; linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΔ hL) ht.le,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (fresh_allow hΔ (α:=α)) hH) ht.le]
  refine Cost.enlarge (Cost.sum (hk x) ((hit_scale (hitPower_pos p G α Δ) hl) x)) ?_
  unfold softNeed; exact add_le_add_right (mul_le_mul_of_nonneg_right (hit_allow hΔ) hD) _

omit hs h1 in
include h in
include hw hx hc in
theorem renew {δ γ : ℝ} (hn : 20 < n.val) (hF : Fees G p c σ C α H w δ γ) : Ingredients (shelves X R p)
    (fill X R c p v α (delta (X.read v))) p δ γ := by
  let Δ := delta (X.read v); let Y := shelves X R p; let d := fill X R c p v α Δ
  have hΔ := delta_bound g h.projects
  obtain ⟨u,hu,hb⟩ := h.cheap
  obtain ⟨k,hk,hK⟩ := h.expensive
  obtain ⟨he,hL⟩ := quote_family hx hc hw α _ hu hb hΔ
  obtain ⟨m,κ,hm,hR⟩ := hF.hard
  have hQ (i : ℕ) := quote_soft (R:=R) (c:=c) g α Δ hu h.smooth (numbering _ i)
  exact Payments.tender (h.fittings g hx hc hn α Δ)
    (show (Y.pours d).EBound p δ from ⟨_,fun i => quote_regular g hx hc α Δ hu h.smooth (numbering _ i),fun x =>
      Cost.equiv (numbering _) (Cost.enlarge (he x) hF.regular)⟩)
    (show Payments.hardCost p Y k w from ⟨fun i => (hk i).1,hK⟩) ⟨fun i => (norm_nonneg _).trans (hQ i 1),fun x =>
      Cost.equiv (numbering _) (Cost.enlarge (hL x) hm)⟩ (fun i U => ⟨(hk i).2 U,hQ i U⟩) hR

end Local
end YM.AnalyticBridge.VerifiedReset.Collection
