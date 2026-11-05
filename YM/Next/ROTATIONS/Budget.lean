import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import YM.Compact.State
import YM.Heat.Rows
import YM.Mink.Poincare
/-! # Subpower accounting. No arity/history claims; a single sequence ε = exp(-n). -/
noncomputable section
namespace YM.Outer
open Filter Function Set Asymptotics
open scoped Topology BigOperators NNReal ENNReal ContDiff

def fuel (v : ℝ) (n : ℕ) := Real.exp (n*v)
lemma fuel_pos (v n) : 0 < fuel v n := Real.exp_pos _
lemma fuel0 (n) : fuel 0 n=1 := by simp [fuel]
lemma fuel_neg (v n) : fuel (-v) n=(fuel v n)⁻¹ := by simp [fuel, Real.exp_neg]
lemma fuel_mul (v w n) : fuel v n*fuel w n=fuel (v+w) n := by rw [fuel,fuel,← Real.exp_add,← mul_add]; rfl
lemma fuel_rate (v n) (k : ℕ) : fuel v n^k=fuel (v*k) n := by
  induction k with
  | zero => simp [fuel0]
  | succ k ih => rw [pow_succ,ih,fuel_mul,Nat.cast_add,Nat.cast_one,mul_add,mul_one]
lemma fuel_le {v w} (h : v≤w) (n) : fuel v n ≤ fuel w n := Real.exp_le_exp.mpr (by gcongr)
lemma fuel_grows {v} (h : 0<v) : Tendsto (fuel v) atTop atTop := Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const h)
lemma fuel_falls {v} (h : v<0) : Tendsto (fuel v) atTop (𝓝 0) := by
  have he := fuel_grows (neg_pos.mpr h) |>.inv_tendsto_atTop
  refine he.congr (fun i => ?_); rw [Pi.inv_apply,fuel_neg,inv_inv]
lemma bigger {a b : ℝ} (h : a<b) (C : ℝ) : ∀ᶠ i : ℕ in atTop, fuel a i*C ≤ fuel b i := by
  filter_upwards [(fuel_grows (sub_pos.mpr h)).eventually (eventually_ge_atTop C)] with i hi
  exact (mul_le_mul_of_nonneg_left hi (fuel_pos a i).le).trans_eq (by rw [fuel_mul,add_sub_cancel])

section
variable {X : Type*} [SeminormedAddCommGroup X]
def Budget (a : ℝ) (f : ℕ → X) := ∃ C : ℝ,0≤C ∧ ∀ᶠ i : ℕ in atTop, ‖f i‖ ≤ C*fuel a i
variable {f g : ℕ→X} {x y : ℝ}
lemma Budget.rise (h : Budget x f) (he : x≤y) : Budget y f := by
  obtain ⟨C,hC,h⟩ := h; exact ⟨C,hC,h.mono fun i hi => hi.trans (mul_le_mul_of_nonneg_left (fuel_le he _) hC)⟩
lemma Budget.add (h : Budget x f) (t : Budget x g) : Budget x (fun i => f i+g i) := by
  obtain ⟨C,hC,h⟩ := h; obtain ⟨D,hD,t⟩ := t; refine ⟨C+D,add_nonneg hC hD,?_⟩
  filter_upwards [h,t] with i hi hk; exact (norm_add_le ..).trans ((add_le_add hi hk).trans_eq (add_mul ..).symm)
lemma Budget.neg (h : Budget x f) : Budget x (fun i => -f i) := by
  obtain ⟨C,hC,h⟩ := h; exact ⟨C,hC,by simpa using h⟩
lemma Budget.sub (h : Budget x f) (t : Budget x g) : Budget x (fun i => f i-g i) := by
  simp_rw [sub_eq_add_neg]; exact h.add t.neg
lemma constant_budget (w : X) : Budget 0 (fun _ => w) := ⟨‖w‖,norm_nonneg _,Eventually.of_forall fun i => by simp [fuel0]⟩
lemma no_budget (v : ℝ) : Budget v (fun _ => (0:X)) := ⟨0,le_rfl,by simp⟩
lemma Budget.reduce {Y : Type*} [SeminormedAddCommGroup Y] {F : ℕ→Y} (h : Budget x f) (hh : ∀ᶠ n in atTop, ‖F n‖ ≤ ‖f n‖) : Budget x F := by
  obtain ⟨C,hC,h⟩ := h; refine ⟨C,hC,?_⟩
  filter_upwards [hh,h] with i hi hh; exact hi.trans hh
lemma Budget.limits (h : Budget x f) (hx : x<0) : Tendsto f atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall (fun i => norm_nonneg _)) h ?_
  simpa using (fuel_falls hx).const_mul C
lemma Budget.same (h : Budget x f) (hh : f=ᶠ[atTop] g) : Budget x g := h.reduce (hh.mono fun _ hi => Eq.le (congr_arg norm hi).symm)
lemma budget_sum {ι : Type*} (s : Finset ι) (F : ι → ℕ → X) (a) (h : ∀ i∈s,Budget a (F i)) : Budget a (fun n => ∑ i∈s,F i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact no_budget _
  | @insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun _ v => h _ (by simp [v]))
end
variable {x y : ℝ}
lemma Budget.priced {X : Type*} [SeminormedAddCommGroup X] {F : ℕ → X} {f : ℕ → ℝ}
    (h : Budget x f) (hh : ∀ᶠ i in atTop, ‖F i‖ ≤ f i) : Budget x F := h.reduce (hh.mono fun _ hi => hi.trans (le_abs_self _))
lemma Budget.signed {f g : ℕ→ℝ} (h : Budget x f) (hg : ∀ᶠ i in atTop, 0 ≤ g i) (hh : ∀ᶠ i in atTop, g i≤f i) : Budget x g := by
  apply h.priced; filter_upwards [hg,hh] with i hi he; simpa [Real.norm_of_nonneg hi] using he
lemma Budget.prod {X : Type*} [SeminormedRing X] {f g : ℕ → X} (h : Budget x f) (l : Budget y g) : Budget (x+y) (fun n => f n*g n) := by
  obtain ⟨C,hC,h⟩ := h; obtain ⟨D,hD,l⟩ := l
  refine ⟨C*D,mul_nonneg hC hD,?_⟩
  filter_upwards [h,l] with n hx hy
  refine (norm_mul_le ..).trans ((mul_le_mul hx hy (norm_nonneg _) (hx.trans' (norm_nonneg _))) |>.trans_eq ?_)
  rw [← fuel_mul]; ring
lemma Budget.times {X : Type*} [SeminormedRing X] {f : ℕ → X} (h : Budget x f) (c : X) : Budget x (fun n => c*f n) := by
  simpa only [zero_add] using (constant_budget c).prod h
lemma Budget.pow {f : ℕ → ℝ} (h : Budget x f) (n : ℕ) : Budget (x*n) (fun i => f i^n) := by
  induction n with
  | zero => simp_rw [pow_zero, Nat.cast_zero,mul_zero]; exact constant_budget _
  | succ n ih => simp_rw [pow_succ,Nat.cast_add,Nat.cast_one,mul_add,mul_one]; exact ih.prod h
lemma budget_fuel (a) : Budget a (fuel a) := ⟨1,zero_le_one,Eventually.of_forall fun i => by simp [abs_of_pos (fuel_pos ..)]⟩
lemma budget_inv (a) : Budget (-a) (fun i => (fuel a i)⁻¹) := by simp_rw [← fuel_neg]; exact budget_fuel _
end YM.Outer
