import YM.Push.LOOP_COEFFICIENT.ContinuumTrace


/-!
# Real-frequency exterior gap including the longitudinal column
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Fine
open Matrix Function Set Lattice Laurent RG Wilson Precision Exterior Bloch Bid   Kernel Complex
open scoped Topology BigOperators ComplexOrder
variable {G : Gauge} {a b : Type} [Fintype a] [Fintype b] {k : Momentum}



def deltaFreq (k : Momentum) := ∑ i,‖q k i‖^2
lemma delta_nonneg (k : Momentum) : 0≤deltaFreq k := Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma q_bar (hk : star k=k) (i : Axis) : q (-k) i = star (q k i) := by unfold q; rw [star_sub,star_one,Complex.star_def,← exp_conj,map_mul,conj_I, show (starRingEnd ℂ) (k i) = k i from congr_fun hk i]; simp


lemma delta_gap (hk : star k=k) (h : ∀ i, |(k i).re|≤Real.pi) : (2/Real.pi)^2 * ‖k‖^2 ≤ deltaFreq k := by
  have he : 0<(2/Real.pi:ℝ) := by positivity
  rw [← mul_pow, ← Real.le_sqrt (by positivity) (delta_nonneg _),mul_comm,← le_div_iff₀ he]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_; rw [le_div_iff₀ he]
  refine le_trans ?_ (Real.le_sqrt (norm_nonneg (q k i)) (delta_nonneg k) |>.mpr (Finset.single_le_sum (f:=fun i => ‖q k i‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ _)))
  unfold q; have hR := conj_eq_iff_re.mp (show star (k i) = k i from congr_fun hk i)
  rw [← hR,Complex.norm_real, Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hh := Real.mul_abs_le_abs_sin (x:=(k i).re/2) (by simpa [abs_div] using (show |(k i).re|/2 ≤ Real.pi/2 by gcongr; exact h _))
  rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hh; linarith







-- Quantitative lower numerical bound, no rank or nonempty assumption.
def cash (x : a → ℂ) := (star x ⬝ᵥ x).re












end YM.Push.Loops.Fine
