import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Bingo
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Spat
/-! # Purchases for auxiliary Lap. DO NOT include K/validation slack
 Choose after L and every requested order. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sienna
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable (G : Gauge) (L : Side) {f w : ℝ→ℝ} {p C η l : ℝ} {n : ℕ}
local notation "Z" => (fun t=> betaF G t L)
local notation "M" => (fun t=> Delay.fineMonitor G L t)
local notation "F" => (fun t=> Pressure.fiery G t L)
def vow := -(7/16:ℝ)
lemma vow_ok : vow < 0 := by norm_num [vow]
def eaves (x:ℝ):= Z x ^ vow
def furl (x:ℝ):= Z x ^ (- (1:ℝ)) -- microscopy width z^-1
def wick (d t:ℝ):= d* Delay.fineMonitor G L t
local notation "U" => eaves G L
local notation "δ" => furl G L
local notation "D" => wick G L
lemma edge : Rate G L vow (U) := Rate.power
lemma belt : Rate G L (-1) (δ) := Rate.power
lemma gen (d:ℝ) : Rate G L 0 (D d) := Rate.monitor.mul_left _
lemma below' (h : Rate G L η f) (he:η<0) (hp : 0 < p) : ∀ᶠ x in atTop, f x<p := by
  filter_upwards [h.below he (p/2) (by positivity)] with x hx using ((le_abs_self _).trans hx).trans_lt (half_lt_self hp)
lemma contraction {a d b : ℝ} (hb : 0 < b) (hp : Rate G L p f) (h:p<d) : ∀ᶠ t in atTop, a*f t<b * Z t ^ d := by
  have he := below' G L ((hp.mul_left a).mul (Rate.power (G:=G) (L:=L) (a:=-d))) (by linarith) hb
  filter_upwards [Delay.shift_pos G L,he] with t ht hv
  rw [Real.rpow_neg ht.le] at hv; simpa only [mul_comm b] using (mul_inv_lt_iff₀ (Real.rpow_pos_of_pos ht _)).mp hv

lemma gift : Bolt G L (Delay.bill G L) := ⟨1,1,zero_le_one, Eventually.of_forall fun x=>by rw [one_mul,pow_one, abs_of_nonneg (zero_le_one.trans (Delay.bill_ge ..))]⟩
lemma fires {d : ℝ} (hd : 0 < d) (hb:Bolt G L f) (h : Bolt G L w) : ∀ᶠ t in atTop, f t+w t*M t ≤ d*M t^2 := by
  let E:= Delay.fineMonitor G L
  filter_upwards [hb.listens (show 0<(1/2:ℝ) by norm_num),h.listens (show 0 < (1/2:ℝ) by norm_num), (Bolt.still (2/d)).listens (G:=G) (L:=L) (show 0 < (1/2:ℝ) by norm_num)] with t ht hv he
  rw [← Real.sqrt_eq_rpow] at ht hv he
  let m:= E t; let y := Real.sqrt m
  have hp:1 ≤ m:=Real.one_le_exp (sq_nonneg _)
  have hR: 2/d≤y:=(le_abs_self _).trans he; have hy: y^2=m:= Real.sq_sqrt (zero_le_one.trans hp)
  have hs : 2≤ d*y := by simpa only [mul_comm d] using (div_le_iff₀ hd).mp hR
  apply le_trans (add_le_add ((le_abs_self _).trans ht) (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hv) (zero_le_one.trans hp)))
  change y+y*m ≤ d*m^2; nlinarith only [hp,hy,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg m)) (zero_le_one.trans hp),mul_nonneg (Real.sqrt_nonneg m) (sub_nonneg.mpr hp), show (d*(y*y))*m=d*m^2 by (rw [← sq,hy]; ring)]


lemma lamp {t : ℝ} (ht : 0< Z t) (β:ℝ) (hb : Z t/2 ≤ β) : 0<gStep β ∧ gStep β ≤ 2*gStep (Z t) := by
  have hh : 0<β:=(half_pos ht).trans_le hb
  have hx:= Fare.gS (Z t) ht; have hp := Fare.gS β hh
  refine ⟨hp.1,?_⟩; apply (sq_le_sq₀ hp.1.le (show 0≤ 2*gStep (Z t) from mul_nonneg (by norm_num) hx.1.le)).1
  apply le_of_mul_le_mul_right _ ht; rw [mul_pow, mul_assoc, hx.2,mul_one]
  nlinarith only [mul_le_mul_of_nonneg_left hb (sq_nonneg (gStep β)), hp.2]
lemma glim : Rate G L (-(1/2)) (fun t=> 2*gStep (Z t)) := Rate.mul_left (by
  refine Rate.congr Rate.power ?_; filter_upwards [Delay.shift_pos G L] with t ht; rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]; rfl) 2
lemma billsV (d:ℝ) (hd : 0<d) (R r b m : ℝ) (he:0<b) (hc:0<r) (hm:0 < m) : ∀ᶠ t in atTop,
    0<U t ∧ 0<D d t ∧ U t≤1 ∧ R*U t+U t*D d t < m ∧ U t < b ∧ Uniform.shade G*(R*U t+U t*D d t)≤r/2 ∧ ∀ β, Z t/2 ≤ β → 0 < gStep β ∧ gStep β < U t := by
  have hp := (edge G L|>.mul_left R).add (by rw [← add_zero vow]; exact Rate.mul (edge G L) (gen G L d)); filter_upwards [Delay.shift_pos G L, below' G L (edge G L) vow_ok zero_lt_one, below' G L hp vow_ok hm, below' G L (edge G L) vow_ok he,below' G L (hp.mul_left _) vow_ok (half_pos hc), contraction G L (a:=1) zero_lt_one (glim G L) (show -(1/2:ℝ)<vow by norm_num [vow])] with t ht h' hK hU hR hκ
  exact ⟨Real.rpow_pos_of_pos ht _,mul_pos hd (Delay.monitor_pos G L t),h'.le,hK,hU,hR.le,fun β hb=> ⟨(lamp G L ht β hb).1,(lamp G L ht β hb).2.trans_lt (by simpa only [one_mul,eaves] using hκ)⟩⟩
lemma puff (E c : ℝ) (he : 0<c) : ∀ᶠ t in atTop, E*δ t ≤ c* F t := by
  have h:= contraction G L (a:=1) he ((belt G L).mul_left E) (show -(1:ℝ) < -((1:ℝ)/2) by norm_num)
  filter_upwards [Delay.shift_pos G L,h] with t ht hi
  have hh := le_of_lt hi; simp only [one_mul,Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow] at hh; apply hh.trans; apply mul_le_mul_of_nonneg_left _ he.le; exact le_mul_of_one_le_right (inv_pos.mpr (Real.sqrt_pos.mpr ht)).le (Real.one_le_exp (sq_nonneg _))
end YM.PhysicalNext.Repeat.Sienna
