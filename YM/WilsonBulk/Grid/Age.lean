import YM.Lattice.Scale
import YM.WilsonBulk.Grid.Moment

/-!
# Summation over arbitrary Wilson depths for fixed age demands

Use unshifted log spacing of SAME schedule. Keep `age k W` explicit; `W` is an upper bound
on slow data at the measuring reference (>=1), *not* a chosen power of finer top scale.
Constants in comparing all older/newer ages don't include this reference's price. Triangular
repeated factors exact exponential in scale differences. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Filter Function Set
open Push.AbsoluteSums
open scoped Topology BigOperators Classical
variable (S : Schedule) (a : ℝ)

def damp (i j : ℕ) := Real.exp (a*(S.scale i - S.scale j))

lemma damp_pos (i j) : 0 < damp S a i j := Real.exp_pos _
@[simp] lemma damp_self (i) : damp S a i i = 1 := by simp [damp]
lemma damp_split (i j k) : damp S a i j * damp S a j k = damp S a i k := by
  unfold damp; rw [←Real.exp_add]; congr 1; ring
lemma damp_fuse (i j) (b : ℝ) : damp S a i j * damp S b i j = damp S (a+b) i j := by
  unfold damp; rw [←Real.exp_add]; congr 1; ring
lemma scale_strict : StrictMono S.scale := by
  refine strictMono_nat_of_lt_succ fun i =>?_ ; rw [S.scale_succ]; refine lt_add_of_pos_right _ (Real.log_pos ?_); exact_mod_cast (show 1<(S.block i).val by have h:=S.block_large i; omega)
lemma damp_antitone {i j} (h : i ≤ j) {u : ℝ} (he : a ≤ u) : damp S u i j ≤ damp S a i j :=
  Real.exp_monotone (mul_le_mul_of_nonpos_right he (sub_nonpos_of_le ((scale_strict S).monotone h)))
lemma damp_at (i j : ℕ) : damp S a i j = (S.a j / S.a i) ^ a := by
  unfold damp Schedule.scale; rw [Real.rpow_def_of_pos (div_pos (S.a_pos _) (S.a_pos _)),
    Real.log_div (S.a_pos _).ne' (S.a_pos _).ne', Real.log_inv, Real.log_inv]; congr 1; ring
lemma damp_succ (i : ℕ) : damp S a i (i+1) = ((S.block i).val:ℝ) ^ (-a) := by
  unfold damp; rw [S.scale_succ,Real.rpow_def_of_pos (by positivity)]; congr 1; ring
lemma damp_event {j : ℕ} (h : 0<a) : Tendsto (damp S a j) atTop (𝓝 0) := by
  have he : Tendsto (fun i=> (S.a i / S.a j)^a) atTop (𝓝 0) := by
    simpa only [zero_div, Real.zero_rpow h.ne'] using (((S.shrinks.div_const (S.a j)).rpow_const (Or.inr h.le)))
  simpa only [funext (damp_at S a j)] using he

variable (k : ℕ) (W : ℝ)
/-- eq:kyage. `W = 2+Z`, or another base at least 1. -/
def age (i : ℕ) := W + |S.scale i-S.scale k|
lemma age_ge (i : ℕ) : W ≤ age S k W i := le_add_of_nonneg_right (abs_nonneg _)
lemma age_up {i j : ℕ} (h : i ≤ j) : age S k W j ≤ age S k W i + (S.scale j - S.scale i) := by
  have ht : 0 ≤ S.scale j-S.scale i := sub_nonneg.mpr ((scale_strict S).monotone h)
  unfold age; rw [add_assoc]; refine add_le_add_right ?_ _
  calc _ = |(S.scale i-S.scale k)+(S.scale j-S.scale i)| := by congr 1; ring
       _ ≤ _ := by simpa only [abs_of_nonneg ht] using (abs_add_le (S.scale i-S.scale k) (S.scale j-S.scale i))

lemma age_damp {i j : ℕ} (d : ℕ) (h : i ≤ j) (ha : 0<a) (hW : 1 ≤ W) :
    age S k W j ^ d * damp S a i j ≤ momentWeight a d * age S k W i ^ d := by
  let b := S.scale j-S.scale i
  have hh : 0≤ b := sub_nonneg.mpr ((scale_strict S).monotone h)
  have hi := hW.trans (age_ge S k W i)
  have he : age S k W j ≤ age S k W i * (1+b) :=
    (age_up S k W h).trans (by nlinarith only [hh,hi])
  have hu l := zero_lt_one.trans_le (hW.trans (age_ge S k W l))
  have hz : damp S a i j = (Real.exp (a*b))⁻¹ := by rw [damp,show a*(S.scale i-S.scale j) = -(a*b) by unfold b; ring,Real.exp_neg]
  calc _ ≤ (age S k W i * (1+b))^d * damp S a i j := by
        apply mul_le_mul_of_nonneg_right _ (damp_pos ..).le
        exact pow_le_pow_left₀ (hu _).le he _
       _ ≤ (age S k W i ^d * (momentWeight a d * Real.exp (a*b))) * damp S a i j := by
        rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (damp_pos ..).le
        exact mul_le_mul_of_nonneg_left (polynomial_cost ha hh d) (pow_nonneg (hu i).le d)
       _ = _ := by rw [hz]; field_simp
end YM.WilsonBulk
