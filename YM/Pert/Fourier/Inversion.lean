import YM.Pert.Fourier.Modes
/-! Zero-mode-subtracted scalar Wilson inverse. -/
noncomputable section
namespace YM.Pert.Full
open Lattice Function Complex BigOperators
variable {n : Side}

lemma exp_pair (r : ℝ) : Complex.exp (r*I)+Complex.exp (-(r*I))-2 = ((-4*(Real.sin (r/2))^2:ℝ) :ℂ) := by
  rw [show -(r*I)=(-r:ℝ)*I by simp, Complex.exp_mul_I,Complex.exp_mul_I,← ofReal_cos,← ofReal_cos,← ofReal_sin,← ofReal_sin,Real.sin_neg,Real.cos_neg]
  push_cast
  have he := Real.cos_two_mul' (r/2); have hf : 2*(r/2)=r := by ring
  rw [hf] at he
  have hx : Complex.cos ↑r = 1 - 2*(Complex.sin ((r:ℂ)/2))^2 := by
    norm_cast; have := Real.sin_sq_add_cos_sq (r/2); linarith
  rw [hx]; ring

def topWeight (n : Side) (p : Site n) : ℂ := (n.val:ℂ)^(-4:ℤ) * (delta (moment p) : ℂ)⁻¹
/-- Scalar potential with omitted zero mode. -/
def toroid (x : Site n) : ℂ := ∑ p : Site n, topWeight n p * char p x
lemma scalar_weight (x : Site n) : toroid x = (n.val:ℂ)^(-4:ℤ) * ∑ p, char p x * (delta (moment p):ℂ)⁻¹ := by
  simp_rw [toroid,topWeight,Finset.mul_sum]; apply Finset.sum_congr rfl fun i _ => by ring
lemma second_char (p : Site n) (i : Axis) :
    char p (step i) + char p (-step i)-2 = ((-4*(Real.sin ((moment p i)/2))^2:ℝ) :ℂ) := by rw [char_step,char_neg_step,exp_pair]
lemma char_lap (p x : Site n) : (∑ i, (char p (x+step i)+char p (x-step i)-2 • (char p x))) = char p x * ((-delta (moment p):ℝ):ℂ) := by
  unfold delta; push_cast; simp_rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; rw [(sub_eq_add_neg x), char_add,char_add,two_smul]
  convert! congrArg (char p x * ·) (second_char p i) using 1 <;> push_cast <;> ring
lemma lap_toroid (x : Site n) : (∑ i, (toroid (x+step i)+toroid (x-step i)-2 • (toroid x))) =
    -(n.val:ℂ)^(-4:ℤ) * ((∑ p, char p x) - 1) := by
  classical
  simp only [toroid,two_smul,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp_rw [← two_smul ℕ]
  have eh (a b c t : ℂ) : c * a+c*b-2 • (c*t) = c*(a+b-2 • t) := by simp only [two_smul]; ring
  -- simplify before nsmul issues
  simp_rw [eh,←Finset.mul_sum, char_lap]
  conv_lhs => rw [← Finset.sum_erase_add _ _ (a:=(0:Site n)) (by simp)]
  congr 0
  have hweight : ∀ p : Site n, p ∈ Finset.univ.erase (0:Site n) → (topWeight n p) * (char p x * ↑(-delta (moment p))) = -(n.val:ℂ)^(-4:ℤ) * char p x := by
    intro p hp; unfold topWeight; have ht := (delta_pos (moment_cube p) (moment_ne (Finset.mem_erase.mp hp).1)).ne'
    have he : ((delta (moment p):ℝ):ℂ) ≠ 0 := by exact_mod_cast ht
    push_cast; field_simp
  rw [Finset.sum_congr rfl hweight, ← Finset.mul_sum, ← Finset.sum_erase_add (s:=Finset.univ) (f:=fun p => char p x) (a:=(0:Site n)) (by simp)]
  simp [delta,zero_char,mesh,incVec,moment,Lattice.lift]
lemma lap_eq (x : Site n) : (∑ i, (toroid (x+step i)+toroid (x-step i)-2 • (toroid x))) =
    -(if x=0 then 1 else 0) + (n.val:ℂ)^(-4:ℤ) := by
  rw [lap_toroid]; simp_rw [swap _ x,scan]
  push_cast
  by_cases hx : x=0
  · rw [if_pos hx,if_pos hx]; field_simp; ring
  simp [hx]
lemma toroid_real (x : Site n) : (toroid x).re = ∑ p : Site n, (n.val:ℝ)^(-4:ℤ) * (delta (moment p):ℝ)⁻¹ * Real.cos (corner (lift x) (moment p)) := by
  change reCLM (toroid x) = _
  have he (p : Site n) : reCLM (char p x) = Real.cos (corner (lift x) (moment p)) := by
    conv_lhs => rw [←wrap_lift x,char_wrapped,Complex.exp_mul_I,← ofReal_cos,← ofReal_sin]
    simp only [reCLM_apply,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im]; simp
  have he' (p : Site n) : (char p x).re = _ := he p
  unfold toroid; rw [map_sum]; apply Finset.sum_congr rfl; intro p _; simp only [reCLM_apply,Complex.mul_re,Complex.mul_im,he',topWeight,← Complex.ofReal_natCast,← Complex.ofReal_zpow,← Complex.ofReal_inv,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_mul,add_zero]
lemma corner_neg (p : E4) (x : Cover) : corner (-x) p = -corner x p := by simp [corner,neg_mul]
lemma toroid_even (x : Site n) : (toroid (-x)).re=(toroid x).re := by
  unfold toroid
  congr 0
  have he (p : Site n) : (char p (-x)).re = (char p x).re := by
    rw [←wrap_lift x,←map_neg,char_wrapped,char_wrapped]; simp only [corner_neg, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg]; simp only [reCLM_apply, Complex.add_re, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re]; simp
  change reCLM _ = reCLM _
  rw [map_sum, map_sum]
  simp [Complex.mul_re,he,topWeight,← Complex.ofReal_inv,← Complex.ofReal_zpow, ← Complex.ofReal_natCast]
end YM.Pert.Full
