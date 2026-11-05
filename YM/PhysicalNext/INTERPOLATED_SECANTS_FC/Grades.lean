import YM.Further.LOCAL_LOG_JETS.Windows
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.JetProducts

/-!
Real coupling coordinate and the four powers in the low-deficit spelling.

Coefficients can be normalized at the reference y (never differentiated); the powers here
are of actual beta / y.

These formulae apply only once any actual polynomial isolation &
alignment on full supports has been supplied.

No claim of its existence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open Lattice RG Wilson Filter Function Set Push.AbsoluteSums Push.Local Further.LogJets
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

def lower := Real.sqrt (2:ℝ)⁻¹
def upper := Real.sqrt (2:ℝ)
abbrev closedTimes := Icc lower upper
abbrev times := Ioo lower upper

theorem interval_numbers : (1:ℝ)/2 ≤ lower ∧ lower < upper ∧ upper ≤ 2 := by
  have h : lower^2=(2:ℝ)⁻¹ := Real.sq_sqrt (by norm_num)
  have h' : upper^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  have he : 0≤lower := Real.sqrt_nonneg _; have hu : 0≤upper := Real.sqrt_nonneg _
  refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem positive_time {t : ℝ} (ht : t∈closedTimes) : 0<t := (by linarith only [interval_numbers.1] : 0<lower).trans_le ht.1

def encoded (y t : ℝ) := y*t^2
def decoded (y b : ℝ) := Real.sqrt (b / y)



theorem decode {y b : ℝ} (hy : 0<y) (h : b∈Icc (y/2) (2*y)) : decoded y b∈closedTimes ∧ encoded y (decoded y b)=b := by
  have hh : (2:ℝ)⁻¹ ≤ b/y := (le_div_iff₀ hy).mpr (by linarith [h.1])
  exact ⟨⟨Real.sqrt_le_sqrt hh,Real.sqrt_le_sqrt ((div_le_iff₀ hy).mpr h.2)⟩,by
    rw [encoded,decoded,Real.sq_sqrt ((by norm_num : (0:ℝ) ≤ 2⁻¹).trans hh)]; field_simp⟩

theorem time_dist {y a b : ℝ} (hy : 0<y) (ha : a∈Icc (y/2) (2*y)) (hb : b∈Icc (y/2) (2*y)) :
    |decoded y a-decoded y b| ≤ |a-b|/y := by
  rw [le_div_iff₀ hy]
  let l := decoded y a; let r := decoded y b
  have hsum : 1 ≤ l+r := by
    have h1 : lower ≤ l := (decode hy ha).1.1
    have h2 : lower ≤ r := (decode hy hb).1.1
    linarith [interval_numbers.1]
  change |l-r| * y ≤ _
  rw [← (decode hy ha).2,← (decode hy hb).2]; change |l-r| * y ≤ |y*l^2-y*r^2|
  rw [show y*l^2 - y*r^2 = (l-r)*y*(l+r) by ring,abs_mul,abs_mul,abs_of_pos hy,abs_of_nonneg (zero_le_one.trans hsum)]
  exact le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) hy.le) hsum

abbrev Grade := Fin 4

def multiplier (q : Grade) (b : ℝ) := b^q.val / b

theorem multiplier_time {y : ℝ} (hy : y≠0) (q : Grade) (t : ℝ) : multiplier q (encoded y t / y) = t^(2*q.val)/t^2 := by
  rw [multiplier,encoded,mul_div_cancel_left₀ _ hy, pow_mul]

theorem time_smooth {j : ℕ} {y t : ℝ} (hy : y≠0) (ht : 0<t) (q : Grade) : ContDiffAt ℝ j (fun t => multiplier q (encoded y t / y)) t := by
  simp_rw [multiplier_time hy]; fun_prop (disch := positivity)

theorem multiplier_bound (q : Grade) {a : ℝ} (ha : a∈ Icc (2:ℝ)⁻¹ 2) : |multiplier q a| ≤ 4 := by
  have hi : 0<a := by linarith [ha.1]
  rw [multiplier,abs_of_pos (div_pos (pow_pos hi _) hi)]
  rcases q with ⟨_|q,hq⟩
  · rw [pow_zero]; rw [div_le_iff₀ hi]; linarith [ha.1]
  rw [pow_succ,mul_div_cancel_right₀ _ hi.ne']; exact (pow_le_pow_left₀ hi.le ha.2 q).trans ((pow_le_pow_right₀ one_le_two
    (by omega : q ≤ 2)).trans (by norm_num))

theorem multiplier_change (q : Grade) {a b : ℝ} (ha : a∈ Icc (2:ℝ)⁻¹ 2) (hb : b ∈ Icc (2:ℝ)⁻¹ 2) :
    |multiplier q a-multiplier q b| ≤ |a-b| * 4 := by
  have hi : 0<a := by linarith [ha.1]
  have hj : 0<b := by linarith [hb.1]
  unfold multiplier
  rcases q with ⟨_|q,hq⟩
  · rw [pow_zero,pow_zero,show 1/a-1/b=(b-a)/(a*b) by field_simp,abs_div,abs_of_pos (mul_pos hi hj),div_le_iff₀ (by positivity),abs_sub_comm]
    exact le_mul_of_one_le_right (abs_nonneg _) (show 1 ≤ 4*(a*b) by nlinarith only [ha.1,hb.1]) |>.trans_eq (mul_assoc ..).symm
  rw [pow_succ,pow_succ,mul_div_cancel_right₀ _ hi.ne',mul_div_cancel_right₀ _ hj.ne']
  rcases q with _|⟨_|v⟩
  · simp
  · simp only [Nat.zero_add,pow_one]; linarith [abs_nonneg (a-b)]

  rw [show v=0 by omega,show a^(2:ℕ)-b^(2:ℕ) = (a-b)*(a+b) by ring,abs_mul]; exact mul_le_mul_of_nonneg_left (by
    rw [abs_of_pos (add_pos hi hj)]; linarith [ha.2,hb.2]) (abs_nonneg _)

variable {G : Gauge} {n : Side}
abbrev Powers (G : Gauge) (n : Side) := Grade → Field G n
/-- Input normalized by fine-stage reference (already treated in the coefficients). -/
def polynomial (g : Powers G n) (b : ℝ) := ∑ i, (fun U => multiplier i b * g i U)

lemma scale_chart {U : Config G n} {f : Field G n} {k : ℕ} (h : Chart k f U) (a : ℝ) : Chart k (fun V => a*f V) U := contDiffAt_const.mul h
lemma polynomial_left (g : Powers G n) {k : ℕ} {U : Config G n} (h : ∀ i,Chart k (g i) U)
    (b : ℝ) (l : List (Directions G n)) (hl : l.length ≤ k) : leftDerivs (polynomial g b) l U = ∑ i, multiplier i b * leftDerivs (g i) l U := by
  unfold polynomial
  rw [left_sum _ _ U l (fun i _ => scale_chart (h i) _) hl]
  simp_rw [left_constant_mul]

lemma polynomial_chart {g : Powers G n} {k : ℕ} {U : Config G n} (h : ∀ i,Chart k (g i) U) (b : ℝ) : Chart k (polynomial g b) U := by
  suffices ∀ s : Finset Grade, Chart k (∑ i∈s, (fun U => multiplier i b * g i U)) U from this _
  intro s; induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact contDiffAt_const
  | insert i s hi ih => rw [Finset.sum_insert hi]; exact (scale_chart (h i) _).add ih

lemma shifted_polynomial {y t : ℝ} (hy : y≠0) (ht : t≠0) (g : Powers G n) {k : ℕ} {U : Config G n} (h : ∀ i,Chart k (g i) U)
    (l : List (Directions G n)) (hl : l.length ≤ k) : t^2 * leftDerivs (polynomial g (encoded y t / y)) l U =
      ∑ i, leftDerivs (g i) l U * t^(2*i.val) := by
  rw [polynomial_left g h _ l hl,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [multiplier_time hy]; field_simp

lemma constant_square {t : ℝ} (ht : t∈closedTimes) (j : ℕ) : |iteratedDeriv j (fun t : ℝ => t^2) t| ≤ 8 := by
  have hu : t ≤ 2 := ht.2.trans interval_numbers.2.2
  have h := positive_time ht
  rw [iteratedDeriv_pow]; rcases j with _|⟨_|⟨_|j⟩⟩
  · rw [Nat.descFactorial_zero, Nat.cast_one,one_mul,Nat.sub_zero,abs_of_pos (pow_pos h 2)]; nlinarith
  · norm_num [Nat.descFactorial]; rw [abs_of_pos h]; linarith
  · norm_num [Nat.descFactorial]
  simp

lemma mul_price {n : ℕ} {t a b : ℝ} {f g : ℝ → ℝ} (hf : ContDiffAt ℝ n f t) (hg : ContDiffAt ℝ n g t)
    (ha : ∀ j≤n, |iteratedDeriv j f t| ≤ a) (hb : ∀ j≤n, |iteratedDeriv j g t| ≤ b) :
    |iteratedDeriv n (fun t => f t * g t) t| ≤ 2^n * a * b := by
  rw [iteratedDeriv_fun_mul hf hg]
  refine (Finset.abs_sum_le_sum_abs ..).trans <| (Finset.sum_le_sum (g:=fun i => (n.choose i : ℝ) * a * b) (fun i hi => ?_)).trans_eq ?_
  · have ht := Finset.mem_range.mp hi
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    gcongr
    · exact mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans (ha i (by omega)))
    · exact ha i (by omega)
    exact hb _ (by omega)
  rw [← Finset.sum_mul,← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

lemma killed {t y : ℝ} {j k : ℕ} {g : Powers G n} {U : Config G n} (ht : 0<t) (hy : 0<y)
    (hk : 6<j) (h : ∀ i,Chart k (g i) U) (l : List (Directions G n)) (hl : l.length ≤ k) :
    iteratedDeriv j (fun t => t^2 * leftDerivs (polynomial g (encoded y t / y)) l U) t = 0 := by
  have he : (fun t => t^2 * leftDerivs (polynomial g (encoded y t / y)) l U) =ᶠ[𝓝 t] (fun t : ℝ => ∑ i, leftDerivs (g i) l U * t^(2*i.val)) := by
    filter_upwards [lt_mem_nhds ht] with t ht; exact shifted_polynomial hy.ne' (ne_of_gt ht) g h l hl
  rw [he.iteratedDeriv_eq,iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  apply Finset.sum_eq_zero; intro i _; rw [iteratedDeriv_const_mul_field,iteratedDeriv_pow,Nat.descFactorial_eq_zero_iff_lt.mpr (by
    have hi : i.val < 4 := i.isLt; omega)]
  simp

end YM.PhysicalNext.InterpolatedSecantsFc
