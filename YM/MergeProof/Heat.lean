import YM.MergeProof.Ginger

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Spicy
open AnalyticBridge AnalyticBridge.VerifiedReset VerifiedReset.Time
open Lattice Wilson RG Geo Collection Quotes Residual Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable (G : Gauge) (S : Stage)
open Push.AbsoluteSums
lemma lowSoft_exp {p : BudgetPoint} (h : Same S p) : summer p S.clip S.width S.paths ≤ summer (probe S) S.clip S.width S.paths *(1+p.B)^ (4:ℕ) := by
  let a := S.supportExponent+2
  let C := (Fintype.card Signed:ℝ)*lowerSize S.clip S.paths
  let e := S.width/8; have he : 0 < e := by have := S.width_pos; unfold e; positivity
  have hC : 0 ≤ C := by have := S.clip.quadratic_pos; have := S.paths_pos; unfold C lowerSize; positivity
  let D := Real.exp (a*lowCount)*C*1 * (e⁻¹^ (4:ℕ)*↑(4:ℕ).factorial * Real.exp e) * (1-Real.exp (-e))⁻¹
  have h : 0 ≤ D := by unfold D; have := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr he)); positivity
  unfold summer Footprint.payment Footprint.degreeIncome
  rw [‹Same S p›.2.2]; apply le_trans (b:=D * Footprint.spread 1 p.B) (le_of_eq ?_)
  · calc
      _ ≤ D * ((Footprint.spread 1 (probe S).B:ℝ)*(1+p.B)^ (4:ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ h
        unfold Footprint.spread Animals.ballCost probe; dsimp; push_cast; rw [one_mul,show (81:ℝ)=3^4 by norm_num,← mul_pow]
        gcongr; linarith
      _ = _ := by unfold D; change _ = (Real.exp (a*lowCount)*_*1*_*(e⁻¹^ (4:ℕ)*_*Real.exp e)*(1-Real.exp (-e))⁻¹)*_; unfold C; ring
  dsimp only [a,C,D,e]; ring

lemma fruit_exp {p : BudgetPoint} (h : Same S p) {H : ℝ} (hH : 0 ≤ H) :
    fruit G p H ≤ fruit G (probe S) 1 * (1+p.B)^ (4:ℕ) * H := by
  have he : resetLoss G p = resetLoss G (probe S) := by
    unfold resetLoss multiplier pairBill probe; dsimp; rw [h.1,h.2.1]
  have ht := loss_pos G p
  have hw : 0 ≤ 1 - Real.exp (-(1/2:ℝ)) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  unfold fruit Footprint.payment Footprint.degreeIncome
  rw [h.2.2,← he]; dsimp only [probe]
  let D := Real.exp ((S.supportExponent+2)*81)*resetLoss G p * ((1/2:ℝ)⁻¹^ (4:ℕ) * ↑(4:ℕ).factorial * Real.exp (1/2))*(1-Real.exp (-(1/2)))⁻¹
  have hd : 0 ≤ D := by unfold D; positivity
  calc
    _ = D*Footprint.spread 1 (4*p.B+2)*H := by dsimp [D]; ring
    _ ≤ D*(Footprint.spread 1 (4*1+2)*(1+p.B)^ (4:ℕ))*H := by
      gcongr D*?_ * H
      unfold Footprint.spread Animals.ballCost; push_cast; rw [one_mul,show (28561:ℝ)=13^4 by norm_num,← mul_pow]
      gcongr; linarith
    _ = _ := by dsimp only [D]; ring

lemma fruit_pos : 0 ≤ fruit G (probe S) 1 := by
  have := loss_pos G (probe S); have h : 0 ≤ 1 - Real.exp (-(1/2:ℝ)) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  unfold fruit Footprint.payment Footprint.degreeIncome; positivity

def endcap (U : ℝ) := fruit G (probe S) 1 +
    ((U+1)*2+2⁻¹*pairBill G (probe S)) * summer (probe S) S.clip S.width S.paths
lemma opens_table {p : BudgetPoint} (h : Same S p) {α H U : ℝ} (hα : |α|≤U) (hH : 0 ≤ H) (ht : H ≤ p.threshold^2) :
    opens G p S.clip S.width S.paths α H ≤ endcap G S U * (1+p.B)^ (4:ℕ) * p.threshold := by
  have he : pairBill G p = pairBill G (probe S) := by unfold pairBill probe; dsimp only []; rw [h.1,h.2.1]
  have hu : 0 ≤ U := (abs_nonneg _).trans hα
  have hp := p.threshold_pos; have hP := p.threshold_le; have hr := pair_nonneg G p
  have hx(p: BudgetPoint) : 0 ≤ summer p S.clip S.width S.paths:=by
     let v:=S.width/8; have ht:0<v:=by unfold v; have :=S.width_pos; positivity
     have hh:0 ≤ 1-Real.exp (-v):= sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le))
     have hs:= S.clip.quadratic_pos; have ha:=S.paths_pos; unfold summer Footprint.payment Footprint.degreeIncome lowerSize; unfold v at *; positivity
  have hy : 0 ≤ hitNeed p G α H := by unfold hitNeed; positivity
  have hE := fruit_pos G S
  have h1 : H ≤ p.threshold := by nlinarith
  have hk : hitNeed p G α H ≤ ((U+1)*2+2⁻¹*pairBill G (probe S))*p.threshold := by
    rw [hitNeed,← he]; linarith only [mul_le_mul_of_nonneg_right h1 hr, mul_le_mul_of_nonneg_right (add_le_add hα (div_le_one_of_le₀ ht (by positivity))) hp.le]
  exact (add_le_add ((fruit_exp G S h hH).trans (mul_le_mul_of_nonneg_left h1 (by positivity)))
    (mul_le_mul hk (Spicy.lowSoft_exp S h) (hx _) (hy.trans hk))).trans_eq
      (by unfold endcap; ring)
end YM.Merge.Spicy
