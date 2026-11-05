import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian

/-!
# Exponential of a real affine + quadratic on counting coordinates

At fixed finite period with the very same type and volume as SectorChange.
Necessity includes a possible flat direction: translations of an L¹ function
cost vanishing mass against a decaying test at infinity, whereas if there is
a nonpositive quadratic direction the sum of two opposite translates of the
kernel dominates the kernel everywhere.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch
open Function Filter Set Matrix MeasureTheory Next.SectorChange.Gaussian
open scoped Topology BigOperators ENNReal

section quad
variable {I : Type} [Fintype I]

/-- Counting metric quadratic form (so `force A = quad A⁻¹`). -/
def quad (M : Table I) (x : Vec I) : ℝ := x ⬝ᵥ (M *ᵥ x)

omit [Fintype I] in
lemma star_vec (x : Vec I) : star x = x := by ext; simp

lemma sumsq_pos {x : Vec I} (h : x ≠ 0) : 0 < x ⬝ᵥ x := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp h
  unfold dotProduct
  exact lt_of_lt_of_le (mul_self_pos.mpr (show x i ≠ 0 from hi))
    (Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))
lemma sumsq_nonneg (x : Vec I) : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma quad_pos {M : Table I} (h : M.PosDef) {x : Vec I} (hx : x ≠ 0) : 0 < quad M x := by
  simpa only [star_vec, quad] using (posDef_iff_dotProduct_mulVec.mp h).2 hx
lemma quad_nonneg {M : Table I} (h : M.PosDef) (x : Vec I) : 0 ≤ quad M x := by
  by_cases he : x=0
  · simp [he,quad]
  exact (quad_pos h he).le
omit [Fintype I] in
lemma symm_pos {M : Table I} (h : M.PosDef) : M.IsSymm := Matrix.isHermitian_iff_isSymm.mp h.isHermitian

lemma turn {M : Table I} (h : M.IsSymm) (x y : Vec I) : x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  nth_rw 1 [← h.eq]
  exact Matrix.dotProduct_transpose_mulVec ..

lemma quad_add {M : Table I} (h : M.IsSymm) (x y : Vec I) :
    quad M (x+y) = quad M x + 2*(x ⬝ᵥ (M *ᵥ y)) + quad M y := by
  unfold quad
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, turn h y]
  ring
lemma quad_sub {M : Table I} (h : M.IsSymm) (x y : Vec I) :
    quad M (x-y) = quad M x - 2*(x ⬝ᵥ (M *ᵥ y)) + quad M y := by
  rw [sub_eq_add_neg,quad_add h]
  unfold quad
  rw [Matrix.mulVec_neg,dotProduct_neg,neg_dotProduct,dotProduct_neg]; ring
lemma quad_scale (M : Table I) (u : ℝ) (x : Vec I) : quad M (u • x) = u^2 * quad M x := by
  unfold quad; rw [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]; simp only [smul_eq_mul]; ring

lemma quad_smul (M : Table I) (u : ℝ) (x : Vec I) : quad (u • M) x = u * quad M x := by
  unfold quad; rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
lemma quad_sum (M T : Table I) (x : Vec I) : quad (M+T) x = quad M x + quad T x := by
  unfold quad; rw [add_mulVec,dotProduct_add]
lemma quad_diff (M T : Table I) (x : Vec I) : quad (M-T) x = quad M x - quad T x := by
  unfold quad; rw [sub_mulVec,dotProduct_sub]

/-- No constant term. -/
def exponent (M : Table I) (b x : Vec I) := b ⬝ᵥ x - quad M x / 2
def kernel (M : Table I) (b x : Vec I) := Real.exp (exponent M b x)

lemma continuous_exponent (M : Table I) (b : Vec I) : Continuous (exponent M b) := by
  unfold exponent quad Matrix.mulVec dotProduct; fun_prop
lemma continuous_kernel (M : Table I) (b : Vec I) : Continuous (kernel M b) :=
  Real.continuous_exp.comp (continuous_exponent M b)
lemma kernel_pos (M : Table I) (b x : Vec I) : 0 < kernel M b x := Real.exp_pos _

variable [DecidableEq I]
lemma unit_det {M : Table I} (h : M.PosDef) : IsUnit M.det := IsUnit.mk0 _ h.det_pos.ne'

lemma complete {M : Table I} (h : M.PosDef) (b z : Vec I) :
    exponent M b z = exponent M 0 (z-M⁻¹ *ᵥ b) + quad M⁻¹ b / 2 := by
  have he : M *ᵥ (M⁻¹ *ᵥ b)=b := by rw [mulVec_mulVec,M.mul_nonsing_inv (unit_det h),one_mulVec]
  unfold exponent
  rw [quad_sub (symm_pos h), he,zero_dotProduct, dotProduct_comm b z]
  unfold quad; rw [he,dotProduct_comm (M⁻¹ *ᵥ b) b]; ring

/-- The unnormalized quadratic calculation, proved FROM the bona fide
probability Gaussian. Positivity of the precision is not optional. -/
theorem kernel_paid {M : Table I} (h : M.PosDef) (b : Vec I) :
    Integrable (kernel M b) ∧ (∫ z, kernel M b z) = coat M⁻¹ * Real.exp (quad M⁻¹ b/2) := by
  let C := M⁻¹
  let f := kernel M (0 : Vec I)
  have hp : C.PosDef := h.inv
  -- centered volume price (under_cloud with a compensating exponent)
  have he (x : Vec I) : Real.exp (force C x / 2) • f x = (1:ℝ) := by
    unfold f kernel exponent force quad C
    rw [M.nonsing_inv_nonsing_inv (unit_det h), zero_dotProduct,zero_sub,smul_eq_mul,← Real.exp_add]
    simp
  obtain ⟨hg,hg'⟩ := under_cloud hp f
  dsimp only at hg hg'; simp_rw [he] at hg hg'
  have hf := hg.mpr (integrable_const _)
  have hv : (∫ z,f z)=coat C := by simpa using hg'
  let m := M⁻¹ *ᵥ b
  have ht : Integrable (fun z => f (-m+z)) := by
    let e := MeasurableEquiv.addLeft (-m)
    have hu : MeasurePreserving e volume volume := measurePreserving_add_left ..
    exact (hu.integrable_comp_emb e.measurableEmbedding).mpr hf
  have hu : kernel M b = fun z => f (-m+z)*Real.exp (quad C b/2) := by
    funext z; unfold kernel; rw [complete h,Real.exp_add,sub_eq_neg_add]; rfl
  simp_rw [show ∀ z, kernel M b z = _ from congrFun hu, integral_mul_const, integral_add_left_eq_self, hv]; rw [hu]; exact ⟨ht.mul_const _,rfl⟩

end quad

section necessity
variable {I : Type} [Fintype I]

private def cutoff (x : Vec I) := Real.exp (-‖x‖)
private lemma cutoff_cont : Continuous (cutoff (I:=I)) := by unfold cutoff; fun_prop
private lemma cutoff_pos (x : Vec I) : 0 < cutoff x := Real.exp_pos _
private lemma cutoff_le (x : Vec I) : cutoff x ≤ 1 := Real.exp_le_one_iff.mpr (by simp)

/-- Translations against an everywhere-positive decaying test. -/
private theorem drifting {f : Vec I → ℝ} (hf : Integrable f) {v : Vec I} (hv : v ≠ 0) :
    Tendsto (fun n : ℕ => ∫ x, f ((n:ℝ) • v + x) * cutoff x) atTop (𝓝 0) := by
  let u (n : ℕ) := (n:ℝ) • v
  let F (n : ℕ) := fun x : Vec I => f x * cutoff (-u n+x)
  have hF (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    hf.aestronglyMeasurable.mul (cutoff_cont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  have hB n : ∀ᵐ x ∂volume, ‖F n x‖ ≤ ‖f x‖ := Eventually.of_forall fun x => by
    unfold F; rw [norm_mul,Real.norm_of_nonneg (cutoff_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) (cutoff_le _)
  have hL : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 0) := Eventually.of_forall fun x => by
    have he : Tendsto (fun n => ‖-u n+x‖) atTop atTop := by
      refine tendsto_atTop.mpr fun a => ?_
      have ht : Tendsto (fun n => ‖u n‖) atTop atTop := by
        unfold u; simp_rw [norm_smul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
        exact tendsto_natCast_atTop_atTop.atTop_mul_const (norm_pos_iff.mpr hv)
      filter_upwards [ht.eventually_ge_atTop (a+‖x‖)] with n hn
      have hh := norm_sub_norm_le (u n) x
      rw [show -u n+x=-(u n-x) by abel,norm_neg]; linarith
    simpa only [mul_zero,F,cutoff,Function.comp_apply] using ((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp he)).const_mul (f x))
  have h := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖) hF hf.norm hB (f:=fun _=>0) hL
  have he n : (∫ x,F n x)=∫ x, f (u n+x)*cutoff x := by
    rw [← integral_add_left_eq_self (F n) (u n)]; simp [F]
  simp_rw [he,integral_zero] at h; exact h

/-- Integrability forces strict positive definiteness of a symmetric
precision, even in presence of the linear term. -/
theorem kernel_requires {M : Table I} (hM : M.IsSymm) {b : Vec I} (hf : Integrable (kernel M b)) : M.PosDef := by
  classical
  refine posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.isHermitian_iff_isSymm.mpr hM,fun v hv => ?_⟩
  rw [star_vec]; change 0 < quad M v
  by_contra! h
  let f := kernel M b; let u (n : ℕ) := (n:ℝ) • v
  have hc : Continuous f := continuous_kernel M b
  have he z (t : ℝ) : exponent M b (t • v+z) = exponent M b z + t*(b ⬝ᵥ v - v ⬝ᵥ (M *ᵥ z)) - t^2*(quad M v)/2 := by
    unfold exponent; rw [quad_add hM,dotProduct_add,dotProduct_smul,quad_scale,smul_dotProduct]; simp only [smul_eq_mul]; ring
  have hh z (n : ℕ) : f z ≤ f (u n+z)+f (-u n+z) := by
    have ht : exponent M b (u n+z)+exponent M b (-u n+z)≥2*exponent M b z := by
      unfold u; rw [he,←neg_smul,he]; nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (n:ℝ)) h]
    rcases le_total (exponent M b z) (exponent M b (u n+z)) with h1|h1
    · exact (Real.exp_monotone h1).trans (le_add_of_nonneg_right (kernel_pos M b _).le)
    have h2 : f z ≤ f (-u n+z) := Real.exp_monotone (by linarith)
    linarith only [h2, show 0<f (u n+z) from kernel_pos ..]
  let drift (t x : Vec I) := f (t+x)*cutoff x
  have hI (t) : Integrable (drift t) := by
    let e := MeasurableEquiv.addLeft t
    have h0 : MeasurePreserving e volume volume := measurePreserving_add_left ..
    have ht : Integrable (fun x => f (t+x)) := (h0.integrable_comp_emb e.measurableEmbedding).mpr hf
    refine ht.norm.mono' (ht.aestronglyMeasurable.mul cutoff_cont.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    dsimp only [drift]; rw [norm_mul,Real.norm_of_nonneg (cutoff_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) (cutoff_le _)
  have hl (n : ℕ) : (∫ x, drift 0 x) ≤ (∫ x, drift (u n) x) + ∫ x, drift (-u n) x := by
    rw [← integral_add (hI _) (hI _)]
    apply integral_mono (hI _) ((hI _).add (hI _))
    intro z
    change f (0+z)*cutoff z ≤ _
    rw [zero_add]
    simpa [drift,add_mul] using mul_le_mul_of_nonneg_right (hh z n) (cutoff_pos z).le
  have ha : 0 < ∫ x, drift 0 x := integral_pos_of_integrable_nonneg_nonzero (by simp only [drift,zero_add]; exact hc.mul cutoff_cont)
    (hI 0) (fun _ => mul_nonneg (kernel_pos ..).le (cutoff_pos _).le)
    (mul_pos (kernel_pos M b _) (cutoff_pos (0:Vec I))).ne'
  have hz : Tendsto (fun n => ∫ x, drift (-(u n)) x) atTop (𝓝 0) := by
    simpa only [drift,u,smul_neg] using drifting hf (neg_ne_zero.mpr hv)
  have ht := le_of_tendsto_of_tendsto' (tendsto_const_nhds (x:=∫ x, drift 0 x) (f:=atTop))
    ((drifting hf hv).add hz) hl
  linarith only [ha, ht]

-- includes the zero-dimensional case
theorem kernel_integrable_iff {M : Table I} (hM : M.IsSymm) (b : Vec I) :
    Integrable (kernel M b) ↔ M.PosDef := by
  classical
  exact ⟨kernel_requires hM,fun hp => (kernel_paid hp b).1⟩
end necessity
end YM.SectorTools.PhysicalGaussianSwitch
