import YM.Push.LOOP_COEFFICIENT.AliasJets
import YM.Push.LOOP_COEFFICIENT.LoopRow

/-!
# Passing between Fourier derivative and quadratic loop-array moments
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Filter Function Set Lattice Laurent Bloch RG Complex Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {σ C : ℝ} {c : On Axis ℝ}

lemma within_ray (hs : 0≤σ) (i : Axis) {z : ℂ} (h : z∈closedBall (0:ℂ) σ) : Within σ (z • unitAxis i) := by
  have hz := (abs_im_le_norm z).trans (show ‖z‖≤σ by simpa using h)
  intro j; by_cases he : j=i <;> simp [unitAxis, *]
lemma mode_ray (i : Axis) (v : Cover) (t : ℂ) : mode (t • unitAxis i) v = Complex.exp (I * (t * v i)) := by simp [mode,unitAxis, Pi.single_apply,mul_ite,ite_mul]
lemma mode_ray_deriv (i : Axis) (v : Cover) (t : ℂ) : HasDerivAt (fun t : ℂ => mode (t • unitAxis i) v) (mode (t • unitAxis i) v * (I * v i)) t := by
  simp_rw [mode_ray]; simpa using (((hasDerivAt_id' t).mul_const (v i : ℂ)).const_mul I).cexp

lemma axis_le_size (v : Cover) (i : Axis) : ‖(v i:ℂ)‖ ≤ size v := by
  have he := Finset.single_le_sum (fun j (_:j∈Finset.univ) => Nat.zero_le (v j).natAbs) (Finset.mem_univ i)
  rw [Complex.norm_intCast,← Int.cast_abs, ← Int.natCast_natAbs,Int.cast_natCast]; exact Nat.cast_le.mpr he

lemma size_exp_bound (v : Cover) (hσ : 0<σ) : (size v:ℝ) * Real.exp (σ/2 * size v) ≤ (2/σ) * Real.exp (σ * size v) := by
  rw [show σ * (size v:ℝ) = (σ/2*size v)+(σ/2*size v) by ring,Real.exp_add,← mul_assoc]; gcongr
  have := Real.add_one_le_exp (σ/2 * size v); rw [div_mul_eq_mul_div,le_div_iff₀ hσ]; linarith

lemma readJetC {c : On Axis ℂ} (hσ : 0<σ) (h : Width σ C c) (i : Axis) : HasDerivAt (fun t : ℂ => Laurent.read c (t • unitAxis i))
    (I * (∑' z : Cover,(z i : ℂ)*c z)) 0 := by
  let g v (t : ℂ) := mode (t • unitAxis i) v * (c v : ℂ)
  let d (v : Cover) (t : ℂ) := (mode (t • unitAxis i) v * (I * (v i:ℂ))) * (c v : ℂ)
  have hd v z (hz : z∈ball (0:ℂ) (σ/2)) : ‖d v z‖ ≤ (2/σ) * (Real.exp (σ*size v) * ‖c v‖) := by
    dsimp only [d]; simp only [norm_mul,Complex.norm_I,mul_one,← mul_assoc]
    refine mul_le_mul_of_nonneg_right (le_trans ?_ (size_exp_bound v hσ)) (norm_nonneg _)
    rw [mul_comm]; exact mul_le_mul (axis_le_size v i) (reward _ _ _ (within_ray (half_pos hσ).le i (ball_subset_closedBall hz))) (norm_nonneg _) (by positivity)
  have he := hasDerivAt_tsum_of_isPreconnected (g:=g) (h.2.1.mul_left (2/σ)) isOpen_ball (convex_ball (0:ℂ) (σ/2)).isPreconnected (fun v z _ => (mode_ray_deriv i v z).mul_const (c v : ℂ)) hd (mem_ball_self (half_pos hσ)) (by simpa [g] using! h.summable hσ.le) (mem_ball_self (half_pos hσ))
  change HasDerivAt (fun z => ∑' v, g v z) (∑' v,d v 0) 0 at he
  simp_rw [d,zero_smul,mode_constant,one_mul,mul_assoc, tsum_mul_left] at he; exact he

lemma readJet (hσ : 0<σ) (h : Width σ C c) (i : Axis) : HasDerivAt (fun t : ℂ => Laurent.read (fun z => (c z : ℂ)) (t • unitAxis i))
    (I * ((∑' z : Cover,(z i : ℝ)*c z : ℝ):ℂ)) 0 := by
  rw [ofReal_tsum]; push_cast; exact readJetC hσ (by simpa [Laurent.Width] using! h : Width σ C fun z => (c z : ℂ)) i

lemma readMomentC_summable {c : On Axis ℂ} (hσ : 0<σ) (h : Width σ C c) (i : Axis) : Summable (fun z : Cover => (z i : ℂ)*c z) := by
  refine Summable.of_norm_bounded (h.2.1.mul_left (2/σ)) fun v => ?_
  rw [norm_mul,← mul_assoc]; refine mul_le_mul_of_nonneg_right (le_trans ?_ (size_exp_bound v hσ)) (norm_nonneg _)
  exact (axis_le_size v i).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))



variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {R : Row a b}
omit [DecidableEq a] in
lemma under_read (hσ : 0<σ) (h : Row.strip R σ C) (hz : ∀ i j, (∑' z,R i j z)=0) (he : ∀ i j (d : Axis), (∑' z : Cover, (z d : ℝ)*R i j z)=0) (p : Momentum) : UnderMatrix (Row.read R) p 2 := by
  intro i j; apply below_succ.mpr
  have hf := analyticComponent (row_analytic h hσ (Work.F07.realStrip _ (half_pos hσ) (star_zero (R:=Momentum)))) i j
  constructor
  · apply below_one; simp only [Row.read,Matrix.of_apply,Laurent.read,mode_constant, one_smul,← ofReal_tsum,hz,ofReal_zero]
  have h0 (d : Axis) := (line_one hf (unitAxis d)).symm
  rw [line_one hf p,← unit_span p, map_sum]; apply Finset.sum_eq_zero; intro d _; rw [map_smul, h0 d,lineD,iteratedDeriv_one,show deriv (fun t : ℂ => R.read (t • unitAxis d) i j) 0 = _ from (readJet hσ (h i j) d).deriv,he,ofReal_zero,mul_zero,smul_zero]



variable {G : Gauge} {W : PathData G} {q : Clip} {Λ : ℝ}
lemma under_loopRow (h : W.Bounds q σ C Λ) : ∀ p, UnderMatrix (Row.read (loopRow W)) p 2 := under_read h.width (loopRow_budget h.width h.two) (fun i j => (loopRow_sum h i j).tsum_eq) (fun i j d => (loopRow_moment h i j d).tsum_eq)
end YM.Push.Loops
