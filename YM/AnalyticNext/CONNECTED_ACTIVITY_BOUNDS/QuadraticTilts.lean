import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.CenteredMarginal
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.ResolventVolume
import YM.Progress.STATIONARY_SCENES.Green

/-!
# Changing just the denominator: exponential moments

E (7360, 6590). One joint marginal, no product of fictitiously
resampled events on separate copies of a link. Real PSD costs on
Counting space. Key is the trace price independent of the ambient volume,
paid just by the actually read addresses, even for LARGE linked sets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Centered
open MeasureTheory Filter Matrix ResolventVolume
open Progress.StationaryScenes
open scoped Topology BigOperators ENNReal Matrix.Norms.Frobenius
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Attach costs only to listed physical coordinates. -/
def tilt (d : n → ℝ) (z : n → ℝ) := ∑ i, d i*(z i)^2

lemma pays_tilt (d z : n → ℝ) : dotProduct z (diagonal d *ᵥ z) = tilt d z := by
  unfold dotProduct tilt
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]; ring

omit [DecidableEq n] in
lemma dot_nonneg (v : n → ℝ) : 0 ≤ dotProduct v v := Finset.sum_nonneg fun _ _ => mul_self_nonneg _

omit [DecidableEq n] in
lemma dot_pos {v : n → ℝ} (h : v ≠ 0) : 0 < dotProduct v v :=
  lt_of_le_of_ne (dot_nonneg v) (fun e => h (dotProduct_self_eq_zero.mp e.symm))

/-- The diagonal weights may share coordinates, not arbitrary uniform over
volume: both the pointwise bound and their ACTUAL sum matter. -/
lemma paid_precision (A : Matrix n n ℝ) (d : n → ℝ) {r u : ℝ} (hA : Green.Bottom A (r+u))
    (hd : ∀ i, 0 ≤ d i) (hh : ∀ i,d i ≤ u) (t : ℝ) (ht : t ≤ 1) :
    Green.Bottom (graph A (-diagonal d) t) r := by
  intro z
  have hp : 0 ≤ tilt d z := Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sq_nonneg _)
  have hx := mul_le_of_le_one_left hp ht
  have hy : tilt d z ≤ u * dotProduct z z := by
    unfold tilt dotProduct; rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← pow_two]; exact mul_le_mul_of_nonneg_right (hh _) (by positivity)
  unfold graph; rw [smul_neg, ← sub_eq_add_neg,Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul,pays_tilt]
  linarith [hA z]

omit [Fintype n] in
lemma pay_sym {A : Matrix n n ℝ} (d : n → ℝ) (ha : A.IsHermitian) (t : ℝ) :
    (graph A (-diagonal d) t).IsHermitian := by
  unfold graph; apply ha.add
  unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_smul, star_trivial,(Matrix.isHermitian_diagonal d).neg.eq]

omit [DecidableEq n] in
lemma symmetric_bottom {A : Matrix n n ℝ} {r : ℝ} (hr : 0<r) (h : Green.Bottom A r) (hh : A.IsHermitian) :
    A.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hh ?_
  intro x he; rw [star_trivial]; exact (mul_pos hr (dot_pos he)).trans_le (h x)

/-- Diagonal-only inverse (without Combes diminution), no extra 2 in
score cost. -/
lemma inverse_read {A : Matrix n n ℝ} {r : ℝ} (hr : 0<r) (h : Green.Bottom A r)
    (hh : A.IsHermitian) (i : n) : (A⁻¹) i i ≤ r⁻¹ := by
  have hp := symmetric_bottom hr h hh
  let x j := (A⁻¹) j i
  have hx : 0 < x i := hp.inv.diag_pos
  have hy j : (A *ᵥ x) j = if j=i then 1 else 0 := by
    calc
      _ = (A * A⁻¹) j i := rfl
      _ = _ := by rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')]; rfl
  have he := h x
  have hd : x i*x i ≤ dotProduct x x := Finset.single_le_sum (f:=fun j => x j*x j)
    (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  have hv : r*(x i*x i) ≤ x i := calc
    _ ≤ r*dotProduct x x := mul_le_mul_of_nonneg_left hd hr.le
    _ ≤ _ := by simpa [dotProduct, hy] using he
  change x i ≤ _; apply le_of_mul_le_mul_left _ hr; rw [mul_inv_cancel₀ hr.ne']
  exact le_of_mul_le_mul_right (show r*x i*x i ≤ 1*x i from by simpa [mul_assoc] using hv) hx

lemma bill_interp_lower {A : Matrix n n ℝ} {d : n → ℝ} {r u : ℝ} (hr : 0 < r)
    (ha : A.IsHermitian) (hA : Green.Bottom A (r+u)) (hd : ∀ i, 0 ≤ d i) (hh : ∀ i, d i ≤ u) :
    -(r⁻¹ * ∑ i, d i) ≤ Real.log (A-diagonal d).det - Real.log A.det := by
  have hf t (ht : t ∈ Set.Icc (0:ℝ) 1) : (graph A (-diagonal d) t).det ≠ 0 :=
    (symmetric_bottom hr (paid_precision A d hA hd hh t ht.2) (pay_sym _ ha t)).det_pos.ne'
  let g (t : ℝ) := Matrix.trace ((graph A (-diagonal d) t)⁻¹ * (-diagonal d))
  have hg : ContinuousOn g (Set.uIcc 0 1) :=
    (show Continuous fun x : Matrix n n ℝ => trace x from continuous_id.matrix_trace).comp_continuousOn
      ((graph_inverse A (-diagonal d) hf).mul continuousOn_const)
  let C : ℝ := r⁻¹ * ∑ i, d i
  -- Don't take an absolute-value trace proportional to the volume.
  calc
    _ = ∫ t in (0:ℝ)..1, -C := by simp [C]
    _ ≤ ∫ t in (0:ℝ)..1, g t := by
      refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const hg.intervalIntegrable ?_
      intro t ht; simp only [g,Matrix.mul_neg,trace_neg,neg_le_neg_iff]
      unfold Matrix.trace Matrix.diag C
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by rw [Matrix.mul_diagonal]
                                            apply mul_le_mul_of_nonneg_right _ (hd i)
                                            exact inverse_read hr (paid_precision A _ hA hd hh t ht.2) (pay_sym _ ha t) i
    _ = _ := by rw [sub_eq_add_neg A]; exact invoice A (-diagonal d) hf

/-- Full-volume normalization in force while tilting. Exact, no inequality on
an assumed partition function. -/
theorem tilted_exact {A : Matrix n n ℝ} (d : n → ℝ) (ha : A.PosDef)
    (h : (A-diagonal d).PosDef) :
    Integrable (fun z => Real.exp (tilt d z/2)) (law A) ∧
      (∫ z, Real.exp (tilt d z/2) ∂law A) = Real.exp ((Real.log A.det - Real.log (A-diagonal d).det)/2) := by
  let _ := probability ha
  have he z : density A z * Real.exp (tilt d z/2) = (bill A)⁻¹ * heat (A-diagonal d) z := by
    unfold density heat
    rw [mul_assoc, ← Real.exp_add, Matrix.sub_mulVec, dotProduct_sub, pays_tilt]
    ring_nf
  have hb : (bill A)⁻¹ * bill (A-diagonal d) = Real.exp ((Real.log A.det - Real.log (A-diagonal d).det)/2) := by
    apply mul_left_cancel₀ (bill_pos A).ne'; rw [mul_inv_cancel_left₀ (bill_pos A).ne']
    unfold bill; rw [mul_assoc, ← Real.exp_add]; ring_nf
  rw [pays_L1, integrates]; simp_rw [smul_eq_mul, he]; rw [integral_const_mul,Gaussian_bill h,hb]
  exact ⟨(heat_integrable h).const_mul _,rfl⟩

theorem tilted {A : Matrix n n ℝ} {d : n → ℝ} {r u : ℝ} (hr : 0 < r)
    (ha : A.IsHermitian) (hA : Green.Bottom A (r+u)) (hd : ∀ i, 0 ≤ d i) (hh : ∀ i, d i ≤ u) :
    Integrable (fun z => Real.exp (tilt d z/2)) (law A) ∧
      (∫ z, Real.exp (tilt d z/2) ∂law A) ≤ Real.exp ((r⁻¹ * ∑ i, d i)/2) := by
  have he (t) (ht : t ≤ 1) := symmetric_bottom hr (paid_precision A d hA hd hh t ht) (pay_sym _ ha t)
  obtain ⟨hz,h⟩ := tilted_exact (A:=A) d (by simpa [graph] using he 0 zero_le_one)
    (by simpa [graph,sub_eq_add_neg] using he 1 le_rfl)
  refine ⟨hz,h.trans_le (Real.exp_monotone ?_)⟩; linarith [bill_interp_lower hr ha hA hd hh]
end YM.AnalyticNext.ConnectedActivity.Centered
