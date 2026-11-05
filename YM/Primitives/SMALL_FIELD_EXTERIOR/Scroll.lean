import YM.Primitives.SMALL_FIELD_EXTERIOR.Squares

/-!
# Finite-dimensional range estimates en route

Because the box is compact and nonnegative Hessian charge holds while steering,
we can afford crude comparisons *to prove density of the range*. This
costs volume, NOT a method to infer the estimate on BL constants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
variable {ι : Type} [Fintype ι]
variable {V H u v : Points ι → ℝ} {r K : ℝ}

lemma size_compare (hV : ContinuousOn V (cube ι r)) (hH : ContinuousOn H (cube ι r))
    (hu : ContinuousOn u (cube ι r)) (h : ∀ x∈cube ι r,H x-V x ≤ K) :
    size r V u ≤ Real.exp (K/2)*size r H u := by
  apply (sq_le_sq₀ (size_nn ..) (mul_nonneg (Real.exp_pos _).le (size_nn ..))).mp
  rw [mul_pow,size_sq,size_sq,sq (Real.exp _), ← Real.exp_add,add_halves]
  unfold bracket raw
  rw [← integral_const_mul]
  apply setIntegral_mono_on (raw_L1 hV (hu.mul hu)) ((raw_L1 hH (hu.mul hu)).const_mul _) (cube_meas _)
  intro x hx
  rw [← mul_assoc,← Real.exp_add]
  exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by linarith [h x hx])) (mul_self_nonneg _)

structure Glide (r : ℝ) (V : Points ι → ℝ) (K : ℝ) : Prop where
  pos : 0<K
  down (t) : t∈Icc (0:ℝ) 1 → ∀ f, ContinuousOn f (cube ι r) → size r (t • V) f ≤ K * size r 0 f
  up (t) : t∈Icc (0:ℝ) 1 → ∀ f, ContinuousOn f (cube ι r) → size r 0 f ≤ K * size r (t • V) f
lemma glide (hr : 0 < r) (hV : ContinuousOn V (cube ι r)) : ∃ K, Glide r V K := by
  obtain ⟨K,h⟩ := (cube_compact r).exists_bound_of_continuousOn hV
  have hk : 0 ≤ K := (norm_nonneg _).trans (h _ (show 0 ∈ cube ι r from Metric.mem_closedBall_self hr.le))
  have he (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : Points ι) (hx : x∈cube ι r) : |(t • V) x| ≤ K := calc
    _ = t* |V x| := by simp [abs_mul,abs_of_nonneg ht.1]
    _ ≤ 1*K := mul_le_mul ht.2 (h x hx) (abs_nonneg _) (by positivity)
    _ = _ := one_mul _
  refine ⟨Real.exp (K/2), Real.exp_pos _, fun t ht f hf => size_compare (continuousOn_const.smul hV) continuousOn_const hf ?_,
    fun t ht f hf => size_compare continuousOn_const (continuousOn_const.smul hV) hf ?_⟩
  · intro x hx
    change 0 - (t • V) x ≤ K; linarith [(abs_le.mp (he t ht x hx)).1]
  intro x hx; change (t • V) x - 0 ≤ K; linarith [(abs_le.mp (he t ht x hx)).2]

lemma pythagoras (hV : ContinuousOn V (cube ι r)) (hu : ContinuousOn u (cube ι r)) (hv : ContinuousOn v (cube ι r))
    (h : bracket r V u v=0) : size r V u ≤ size r V (u+v) := by
  apply (sq_le_sq₀ (size_nn ..) (size_nn ..)).mp
  rw [size_sq,size_sq,bracket_add hV hu hv (hu.add hv), bracket_sym r V u (u+v), bracket_add hV hu hv hu,
    bracket_sym r V v (u+v), bracket_add hV hu hv hv,bracket_sym r V v u,h,add_zero,zero_add]
  linarith only [self_nonneg r V v]
lemma deficit (hV : ContinuousOn V (cube ι r)) (hu : ContinuousOn u (cube ι r)) (hv : ContinuousOn v (cube ι r)) :
    size r V u ≤ size r V v + size r V (v-u) := calc
  _ = size r V (v-(v-u)) := by rw [sub_sub_cancel]
  _ ≤ _ := size_sub hV hv (hv.sub hu)
lemma size_congr (V : Points ι → ℝ) (h : EqOn u v (cube ι r)) : size r V u=size r V v := by
  unfold size bracket; congr 1; apply raw_congr; intro x hx; simp only [Pi.mul_apply,h hx]

variable [DecidableEq ι]

lemma Neumann.free_estimate (hr : 0 ≤ r) (hV : Regular r 2 V) (hh : Charged r V 0) (hk : Glide r V K) (hu : Neumann r u)
    (t) (ht : t∈Icc (0:ℝ) 1) (i : ι) : size r 0 (pc i u) ≤ (2*r)*K * size r (t • V) (elliptic (t • V) u) := by
  have hw : Charged r (t • V) 0 := by simpa only [mul_zero] using hh.smul hV t ht.1
  apply (hu.rough hr i).trans
  rw [mul_assoc (2*r)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (hk.up _ ht _ (((hu.stripe i).tangent i).cOn)).trans
    (mul_le_mul_of_nonneg_left (second_budget hr hu (hV.smul _) hw i i) hk.pos.le)

lemma ceiling_first (hr : 0 ≤ r) (hV : Regular r 2 V) : ∃ A : ι → ℝ, (∀ i, 0 ≤ A i) ∧
    ∀ i x, x∈cube ι r → |pc i V x| ≤ A i := by
  choose A hA using fun i => (cube_compact r).exists_bound_of_continuousOn ((hV.tangent i).cOn)
  exact ⟨A,fun i => (norm_nonneg _).trans (hA i _ (show 0∈cube ι r from Metric.mem_closedBall_self hr)),hA⟩

def drift (V u : Points ι → ℝ) := ∑ i, pc i V * pc i u
lemma under_drift (hV : Regular r 2 V) (u : Points ι → ℝ) (s t : ℝ) :
    EqOn (elliptic (t • V) u-elliptic (s • V) u) ((t-s) • drift V u) (cube ι r) := by
  intro x hx
  unfold elliptic drift
  rw [← Finset.sum_sub_distrib,Finset.smul_sum]
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold row; simp only [Pi.smul_apply,Pi.mul_apply,Pi.sub_apply,smul_eq_mul,pc_smul i t (hV.diff (by norm_num) hx),pc_smul i s (hV.diff (by norm_num) hx)]
  ring

/-- Uniform in t and this test (including the constant target). -/
theorem advance_rate (hr : 0 < r) (hV : Regular r 2 V) (hh : Charged r V 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : Points ι → ℝ, Neumann r u → ∀ t∈Icc (0:ℝ) 1, ∀ c : ℝ,
      size r 0 (drift V u) ≤ K * size r 0 (elliptic (t • V) u + (fun _ => c)) := by
  obtain ⟨K,hk⟩ := glide hr hV.cOn
  obtain ⟨A,hA,h⟩ := ceiling_first hr.le hV
  let C (i : ι) := A i * ((2*r)*K)*K
  have ht i : 0 ≤ C i := mul_nonneg (mul_nonneg (hA i) (by have := hk.pos; positivity)) hk.pos.le
  have hs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => ht i
  refine ⟨(∑ i,C i)+1,by linarith,fun u hu t hv c => ?_⟩
  let W := t • V; let f := elliptic W u+(fun _ => c)
  have hc := (hu.elliptic1 (hV.smul t)).cOn
  have hf : ContinuousOn f (cube ι r) := hc.add continuousOn_const
  have he (i) : ContinuousOn (pc i V * pc i u) (cube ι r) := ((hV.tangent i).mul (hu.stripe i)).cOn
  have hy : size r W (elliptic W u) ≤ K*size r 0 f := calc
    _ ≤ size r W f := pythagoras (hV.smul t).cOn hc continuousOn_const (hu.mean_zero hr.le (hV.smul t) c)
    _ ≤ _ := hk.down _ hv _ hf
  apply (size_sum (V:=0) continuousOn_const Finset.univ (fun i _ => he i)).trans
  apply le_trans _ (mul_le_mul_of_nonneg_right (show ∑ i,C i ≤ (∑ i,C i)+1 by linarith) (size_nn ..))
  rw [Finset.sum_mul]; apply Finset.sum_le_sum
  intro i _
  have hvi : size r 0 (pc i u) ≤ (2*r*K)*(K*size r 0 f) :=
    (hu.free_estimate hr.le hV hh hk _ hv i).trans (mul_le_mul_of_nonneg_left hy (by have := hk.pos; positivity))
  calc
    _ ≤ A i*size r 0 (pc i u) := size_le_mul continuousOn_const (he i) ((hu.stripe (n:=1) i).cOn) (hA i)
      (fun x hx => by rw [Pi.mul_apply,abs_mul]; exact mul_le_mul_of_nonneg_right (h i x hx) (abs_nonneg _))
    _ ≤ A i*((2*r*K)*(K*size r 0 f)) := mul_le_mul_of_nonneg_left hvi (hA i)
    _ = _ := by unfold f W C; ring

/-- Also at fixed volume, enough to make the error form vanish as
we take a limit. Not the final covariance constant. -/
lemma row_size (hr : 0 < r) (hV : Regular r 2 V) (hh : Charged r V 0) (w : ι → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : Points ι → ℝ, Neumann r u → size r V (adjRow w V u) ≤ K * size r V (elliptic V u) := by
  obtain ⟨K,hk⟩ := glide hr hV.cOn
  obtain ⟨A,hA,h⟩ := ceiling_first hr.le hV
  have hK := hk.pos
  let C (i : ι) := w i^2 * (A i * ((2*r)*K)*K + 1)
  have ht (i : ι) : 0 ≤ C i := by unfold C; have := hA i; positivity
  have hs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => ht i
  refine ⟨(∑ i,C i)+1,by linarith,fun u hu => ?_⟩
  have hi i : ContinuousOn (w i^2 • row V i u) (cube ι r) := continuousOn_const.smul ((hu.row1 hV i).cOn)
  apply (size_sum hV.cOn Finset.univ fun i _ => hi i).trans
  apply le_trans _ (mul_le_mul_of_nonneg_right (show ∑ i,C i ≤ (∑ i,C i)+1 by linarith) (size_nn ..))
  rw [Finset.sum_mul]; apply Finset.sum_le_sum
  intro i _
  have he := (hu.stripe (n:=2) i).cOn
  have hc := (hV.tangent i).cOn.mul he
  let B := elliptic V u
  have hv : size r V (pc i u) ≤ K * size r 0 (pc i u) := by
    simpa only [one_smul] using hk.down 1 ⟨zero_le_one,le_rfl⟩ _ he
  have hj : size r 0 (pc i u) ≤ 2*r*K*size r V B := by
    unfold B; simpa only [one_smul] using hu.free_estimate hr.le hV hh hk 1 ⟨zero_le_one,le_rfl⟩ i
  have hJ : size r V (pc i V * pc i u) ≤ A i*(K*(2*r*K*size r V B)) := calc
    _ ≤ A i * size r V (pc i u) := size_le_mul hV.cOn hc he (hA i) fun x hx => by
      rw [Pi.mul_apply,abs_mul]; exact mul_le_mul_of_nonneg_right (h i x hx) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hv.trans (mul_le_mul_of_nonneg_left hj hK.le)) (hA i)
  unfold C
  rw [size_smul, abs_of_nonneg (sq_nonneg _),mul_assoc (w i^2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (size_sub hV.cOn hc (((hu.stripe i).tangent i).cOn)).trans
  apply (add_le_add hJ (second_budget hr.le hu hV hh i i)).trans_eq
  unfold B; ring
end YM.Primitives.SmallFieldExterior
