import YM.AnalyticBridge.VERIFIED_RESET_STEP.Investor
import YM.Push.CUTOFF_PROJECTORS.Along


/-! Stage prices for the local reset conversion (not for producing the atlas).
A **pre-L output-stage** required small fraction on HRGv. Only auxiliary
+3/+1 stronger output exponent IN that call, and includes assigned orders
& powers of this stage even when repeated. Pure polynomial hit taxes in B
and post-L |α| never in the coefficient of that fraction for regular δ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Time
open Lattice Wilson RG Geo Collection Quotes Residual Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable (G : Gauge) (S : Stage)

/-- A dummy radius and threshold, ONLY to compute stage constants. -/
def probe : BudgetPoint where
  power := S.power
  order := S.order
  supportExponent := S.supportExponent
  B := 1
  threshold := 1
  power_ge := S.power_ge
  order_ge := S.order_ge
  exponent_pos := S.price_pos
  B_pos := zero_lt_one
  threshold_pos := zero_lt_one
  threshold_le := le_rfl

def base := resetFee G (probe S) + turnFee (probe S) *
    (lowBase G S.clip (probe S) S.width S.paths + highBase G (probe S) S.width S.paths)
def top := turnFee (probe S) * highBase G (probe S) S.width S.paths
/-- Pre-L permissible conversion fraction of output allowance for this stage. -/
def credit := (64:ℝ)⁻¹ * (1+base G S)⁻¹

def Same (p : BudgetPoint) := p.power = S.power ∧ p.order = S.order ∧ p.supportExponent = S.supportExponent
lemma base_nonneg : 0 ≤ base G S ∧ 0 ≤ top G S := by
  obtain ⟨hl,hh,_⟩ := budget_pos (probe S) G S.clip S.width_pos S.paths_pos.le
  have ht := loss_pos G (probe S); have hc := turnFee_pos (probe S)
  unfold base resetFee top; exact ⟨by positivity,by positivity⟩
lemma credit_pos : 0 < credit G S := by unfold credit; have := (base_nonneg G S).1; positivity
lemma authorized : credit G S ≤ (64:ℝ)⁻¹ ∧ base G S * credit G S ≤ (64:ℝ)⁻¹ := by
  have h := (base_nonneg G S).1
  have hh := le_mul_of_one_le_right (credit_pos G S).le (b:=1+base G S) (by linarith only [h])
  have he : (1+base G S)*credit G S=(64:ℝ)⁻¹ := by unfold credit; field_simp
  constructor <;> linarith [credit_pos G S]

lemma table {p : BudgetPoint} (h : Same S p) (α H : ℝ) :
    regularNeed G p S.clip S.width S.paths α H = base G S*H+top G S*(|α| *p.threshold^3) := by
  unfold regularNeed base top turnFee lowBase highBase anchoredFee lowFee both lowCost rowCost faceCost highFee
    resetFee resetLoss multiplier pairBill probe rowDegree
  dsimp; rw [h.1,h.2.1,h.2.2]; ring

open Push.AbsoluteSums
lemma lowSoft_exp {p : BudgetPoint} (h : Same S p) : lowHard p S.clip S.width S.paths ≤ lowHard (probe S) S.clip S.width S.paths *(1+p.B)^ (4:ℕ) := by
  let a := S.supportExponent+1
  let C := (Fintype.card Signed:ℝ)*lowerSize S.clip S.paths
  let e := S.width/4; have he : 0 < e := by have := S.width_pos; unfold e; positivity
  have hC : 0 ≤ C := by have := S.clip.quadratic_pos; have := S.paths_pos; unfold C lowerSize; positivity
  let D := Real.exp (a*lowCount)*C*1 * (e⁻¹^ (4:ℕ)*↑(4:ℕ).factorial * Real.exp e) * (1-Real.exp (-e))⁻¹
  have h : 0 ≤ D := by unfold D; have := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr he)); positivity
  unfold lowHard Footprint.payment Footprint.degreeIncome
  rw [‹Same S p›.2.2]; apply le_trans (b:=D * Footprint.spread 1 p.B) (le_of_eq ?_)
  · calc
      _ ≤ D * ((Footprint.spread 1 (probe S).B:ℝ)*(1+p.B)^ (4:ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ h
        unfold Footprint.spread Animals.ballCost probe; dsimp; push_cast; rw [one_mul,show (81:ℝ)=3^4 by norm_num,← mul_pow]
        gcongr; linarith
      _ = _ := by unfold D; change _ = (Real.exp (a*lowCount)*_*1*_*(e⁻¹^ (4:ℕ)*_*Real.exp e)*(1-Real.exp (-e))⁻¹)*_; unfold C; ring
  dsimp only [a,C,D,e]; ring

lemma softReset_exp {p : BudgetPoint} (h : Same S p) {H : ℝ} (hH : 0 ≤ H) :
    softReset G p H ≤ softReset G (probe S) 1 * (1+p.B)^ (4:ℕ) * H := by
  have he : resetLoss G p = resetLoss G (probe S) := by
    unfold resetLoss multiplier pairBill probe; dsimp; rw [h.1,h.2.1]
  have ht := loss_pos G p
  have hw : 0 ≤ 1 - Real.exp (-(1:ℝ)) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  unfold softReset Footprint.payment Footprint.degreeIncome
  rw [h.2.2,← he]; dsimp only [probe]
  let D := Real.exp ((S.supportExponent+1)*81)*resetLoss G p * ((1:ℝ)⁻¹^ (4:ℕ) * ↑(4:ℕ).factorial * Real.exp 1)*(1-Real.exp (-1))⁻¹
  have hd : 0 ≤ D := by unfold D; positivity
  calc
    _ = D*Footprint.spread 1 (4*p.B+2)*H := by dsimp [D]; ring
    _ ≤ D*(Footprint.spread 1 (4*1+2)*(1+p.B)^ (4:ℕ))*H := by
      gcongr D*?_ * H
      unfold Footprint.spread Animals.ballCost; push_cast; rw [one_mul,show (28561:ℝ)=13^4 by norm_num,← mul_pow]
      gcongr; linarith
    _ = _ := by dsimp only [D]; ring

lemma soft_pos : 0 ≤ softReset G (probe S) 1 := by
  have := loss_pos G (probe S); have h : 0 ≤ 1 - Real.exp (-(1:ℝ)) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  unfold softReset Footprint.payment Footprint.degreeIncome; positivity

def softCeiling (U : ℝ) := softReset G (probe S) 1 +
    ((U+1)*2+2⁻¹*pairBill G (probe S)) * lowHard (probe S) S.clip S.width S.paths
lemma soft_table {p : BudgetPoint} (h : Same S p) {α H U : ℝ} (hα : |α|≤U) (hH : 0 ≤ H) (ht : H ≤ p.threshold^2) :
    softNeed G p S.clip S.width S.paths α H ≤ softCeiling G S U * (1+p.B)^ (4:ℕ) * p.threshold := by
  have he : pairBill G p = pairBill G (probe S) := by unfold pairBill probe; dsimp only []; rw [h.1,h.2.1]
  have hu : 0 ≤ U := (abs_nonneg _).trans hα
  have hp := p.threshold_pos; have hP := p.threshold_le; have hr := pair_nonneg G p
  have hx := (budget_pos (probe S) G S.clip S.width_pos S.paths_pos.le).2.2
  have hy : 0 ≤ hitNeed p G α H := by unfold hitNeed; positivity
  have hE := soft_pos G S
  have h1 : H ≤ p.threshold := by nlinarith
  have hk : hitNeed p G α H ≤ ((U+1)*2+2⁻¹*pairBill G (probe S))*p.threshold := by
    rw [hitNeed,← he]; linarith only [mul_le_mul_of_nonneg_right h1 hr, mul_le_mul_of_nonneg_right (add_le_add hα (div_le_one_of_le₀ ht (by positivity))) hp.le]
  exact (add_le_add ((softReset_exp G S h hH).trans (mul_le_mul_of_nonneg_left h1 (by positivity)))
    (mul_le_mul hk (lowSoft_exp S h) (budget_pos p G S.clip S.width_pos S.paths_pos.le).2.2 (hy.trans hk))).trans_eq
      (by unfold softCeiling; ring)
end YM.AnalyticBridge.VerifiedReset.Time
