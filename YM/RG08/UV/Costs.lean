import YM.Push.ABSOLUTE_SUMS.Basic
import YM.RG08.Flat.Chain

/-!
# UV report costs
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Laurent Next.Free Matrix
open scoped Topology BigOperators

def age (S : Schedule) (Z : ℝ) (k i : ℕ) : ℝ := 2+Z+|S.scale i-S.scale k|
lemma age_one {S : Schedule} {Z : ℝ} (h : 0≤Z) (k i : ℕ) :
    1 ≤ age S Z k i := by unfold age; linarith [abs_nonneg (S.scale i-S.scale k)]
lemma age_scale_mono (S : Schedule) : Monotone S.scale := by
  refine monotone_nat_of_le_succ (fun i => ?_)
  rw [S.scale_succ]
  linarith [Real.log_nonneg (show (1:ℝ)≤ (S.block i).val by exact_mod_cast (S.block i).property)]
lemma age_larger {S : Schedule} {Z : ℝ} (hz : 0 ≤ Z) (k : ℕ) {i j : ℕ} (h : i ≤ j) :
    age S Z k j ≤ age S Z k i*(1+(S.scale j-S.scale i)) := by
  have ha : age S Z k j ≤ age S Z k i+(S.scale j-S.scale i) := by
    unfold age
    have ht:=abs_add_le (S.scale j-S.scale i) (S.scale i-S.scale k)
    rw [sub_add_sub_cancel,abs_of_nonneg (sub_nonneg.mpr (age_scale_mono S h))] at ht
    linarith
  have ht := age_one (S:=S) hz k i
  nlinarith [age_scale_mono S h]

/-- Exponential in the stipulated unshifted log spacing. -/
def gain (S : Schedule) (v : ℝ) (i N : ℕ) := Real.exp (-v*(S.scale N-S.scale i))

lemma gain_pos (S : Schedule) (v : ℝ) (i N : ℕ) : 0 < gain S v i N := Real.exp_pos _
lemma gain_zero (S : Schedule) (v : ℝ) (i : ℕ) : gain S v i i=1 := by simp [gain]
lemma gain_trans (S : Schedule) (v : ℝ) (i j k : ℕ) :
    gain S v i k = gain S v i j * gain S v j k := by
  unfold gain; rw [← Real.exp_add]; congr 1; ring
lemma gain_spacing (S : Schedule) (v : ℝ) (i N : ℕ) :
    gain S v i N = (S.a N / S.a i) ^ v := by
  have hi := S.a_pos i; have hn := S.a_pos N
  unfold gain Schedule.scale
  rw [Real.log_inv, Real.log_inv, Real.rpow_def_of_pos (by positivity), Real.log_div hn.ne' hi.ne']
  ring_nf
lemma gain_half (S : Schedule) (i N : ℕ) :
    gain S (1/2) i N = Real.sqrt (S.a N / S.a i) := by rw [gain_spacing,Real.sqrt_eq_rpow]
lemma gain_succ_half (S : Schedule) (i : ℕ) :
    gain S (1/2) i (i+1) = 1/Real.sqrt (S.block i).val := by
  have he := S.a_pos i
  rw [gain_half, S.a_step,
    show S.a i / (S.block i).val / S.a i = ((S.block i).val:ℝ)⁻¹ by field_simp,
    Real.sqrt_inv,one_div]
lemma tendsto_gain (S : Schedule) {v : ℝ} (hv : 0 < v) (i : ℕ) :
    Tendsto (gain S v i) atTop (𝓝 0) := by
  have ht : Tendsto (fun k => S.scale k + -S.scale i) atTop atTop :=
    tendsto_atTop_add_const_right _ _ S.divergent
  simp only [← sub_eq_add_neg] at ht
  exact Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (neg_neg_of_pos hv))

/-- Loss from the fine-end polynomial. Keep a true power of the RATIO of spacings. -/
lemma gain_poly (θ μ : ℝ) (h : μ < θ) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Schedule) (Z : ℝ) (k i j : ℕ), 0 ≤ Z → i ≤ j →
      (age S Z k j)^q * gain S θ i j ≤ C*(age S Z k i)^q * gain S μ i j := by
  let v := θ-μ
  have hv : 0<v := sub_pos.mpr h
  let C := v⁻¹ ^ q * q.factorial * Real.exp v
  refine ⟨C,by unfold C; positivity, fun S Z k i j hz hi => ?_⟩
  let a := S.scale j-S.scale i
  have hp : 0 ≤ a := sub_nonneg.mpr (age_scale_mono S hi)
  let b := (age S Z k i)^q
  have hc : 0 ≤ b := pow_nonneg (zero_le_one.trans (age_one hz k i)) _
  have hh : (age S Z k j)^q ≤ b*((1+a)^q) := by
    rw [show b=(age S Z k i)^q from rfl, ← mul_pow]
    exact pow_le_pow_left₀ (zero_le_one.trans (age_one hz k j)) (age_larger hz k hi) q
  calc
    _ ≤ b*(C*Real.exp (v*a))* gain S θ i j := by
      apply mul_le_mul_of_nonneg_right
        (hh.trans (mul_le_mul_of_nonneg_left (Push.AbsoluteSums.polynomial_cost hv hp q) hc))
        (gain_pos ..).le
    _ = b*C*(Real.exp (v*a)*Real.exp (-θ*a)) := by dsimp only [gain,a]; ring
    _ = _ := by rw [← Real.exp_add,show v*a + -θ*a = -μ*a by unfold v; ring, mul_comm b]; rfl

end YM.RG08
