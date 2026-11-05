import YM.MultiNext.VACUUM_STABILITY.Earning.Scale

set_option warningAsError false

/-!
# Per-fixed-stage budget realization test
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Earning
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Desk Component Component.Pasture
open Arrival Arrival.Flock Tune Gauss Tree YM.Push.SectorMeasure Next.Scheduling Jets Hits
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

def blueprint (S : Stage) (x : ℝ) : BudgetPoint where
  order := S.order
  power := S.power
  supportExponent := S.supportExponent
  B := max 1 (Blocks x)
  threshold := 1
  order_ge := S.order_ge
  power_ge := S.power_ge
  exponent_pos := S.price_pos
  B_pos := by omega
  threshold_pos := zero_lt_one
  threshold_le := le_rfl

structure SameStamp (S : Stage) (x : ℝ) (P : BudgetPoint) : Prop where
  order : P.order=S.order
  power : P.power=S.power
  exp : P.supportExponent=S.supportExponent
  sites : P.B = Blocks x

namespace Modest

private lemma sites : Modest fun x => (max 1 (Blocks x):ℕ) := by
  refine period.weaker ?_
  filter_upwards [Clock.counting.eventually_ge_atTop 1] with i hi
  rw [max_eq_right hi]; exact ⟨by positivity,le_rfl⟩

lemma units (S : Stage) : Modest fun x => siteUnit (blueprint S x).B := by
  have h := sites.plus sites; have he := (h.plus (simple zero_le_one)).growPower 4
  simpa only [siteUnit,blueprint,Nat.cast_add,Nat.cast_one] using he

private lemma fee (S : Stage) (m : ℕ) (χ : ℝ) (hc : 1 ≤ χ) : Modest fun x => (Tune.Price.first (blueprint S x) m χ)⁻¹ := by
  let g x := blueprint S x
  let P (i : ℕ) := fun _ : ℝ => (i:ℝ)
  have ht i : Modest (P i) := simple (by positivity)
  have hb : Modest fun x => (Hits.stride (g x).B:ℝ) := by
    simpa only [g,Hits.stride,P,blueprint,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using
      (ht 8).prod (sites.plus (ht 1))
  have hz : Modest fun x => Hits.toll (g x).B := by
    unfold Hits.toll; exact (simple (by norm_num)).prod (((simple (by norm_num)).prod hb).growPower 4)
  have hs : Modest fun x => baseFee (g x) := by
    let q := (((simple zero_le_one).plus hb).growPower S.power).growPower S.order
    exact ((prod q (ht ((S.power+1)*S.order).factorial)).prod (simple (Real.exp_pos 1).le))
  have hg : Modest fun i => logPrice (g i) := hz.prod (hs.prod (simple (by norm_num)))
  have hu : Modest fun i => Tune.Price.levy (g i) m χ := by
    have hp := (simple (show 0≤6*χ by linarith)).prod hs
    exact hz.prod (hp.prod (simple (Real.exp_pos ( (S.supportExponent+2+1+6) * (m:ℝ))).le))
  have hw : Modest fun i => ((Rates.raw (g i))⁻¹) := by
    unfold Rates.raw Rates.window; simp_rw [inv_div,div_inv_eq_mul]
    exact ((simple zero_le_one).plus hg).prod ((simple (by norm_num)).prod (units S))
  change Modest fun x => (Rates.raw (g x)/(2*(1+Tune.Price.levy (g x) m χ)))⁻¹
  simp_rw [inv_div,div_eq_mul_inv]; exact ((simple (by norm_num)).prod ((simple zero_le_one).plus hu)).prod hw


end Modest

/- Conditional scale planning: if the assigned operator/score constants H,C,...
 aren't actually available with these dependencies, cannot use. Stage orders fixed at L, with
 thresholds applied to ACTUAL purchased BudgetPoint. -/



-- The requested `t` of `crossingPrice`, when literals priced with polynomial bills.

end YM.Multi.Vacuum.Earning
