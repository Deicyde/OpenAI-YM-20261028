import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Law

/-!
# Necessity test on exponential quadratics (includes singular boundary)

If integrated over counting-coordinate Lebesgue space and the quadratic
precision isn't positive definite, an affine term doesn't rescue it. Use
translates of a fixed open ball, to also treat precisely flat directions
without any implicit assumption of a noncollapsed slice.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SectorTools.PhysicalGaussianInsertion

open Function Filter Set Matrix MeasureTheory Metric
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian (Vec)
open scoped Topology BigOperators Classical ENNReal

variable {ι : Type} [Fintype ι]

private lemma vanishes {F : Vec ι → ℝ} (hF : Integrable F volume) {v : Vec ι} (hv : v ≠ 0) :
    Tendsto (fun n : ℕ => ∫ x in ball ((n : ℝ) • v) 1, F x) atTop (𝓝 0) := by
  let g (n : ℕ) := (ball ((n : ℝ) • v) 1).indicator F
  have ht := tendsto_integral_of_dominated_convergence (f:=0) (‖F ·‖)
    (fun n : ℕ => (show Integrable (g n) volume from hF.indicator measurableSet_ball).1) hF.norm
  have hh : ∀ n, ∀ᵐ x ∂(volume : Measure (Vec ι)), ‖g n x‖ ≤ ‖F x‖ := by
    intro n; apply Eventually.of_forall
    intro x; by_cases h : x ∈ ball ((n : ℝ) • v) 1 <;> simp [g, h]
  have he : ∀ᵐ x : Vec ι ∂volume, Tendsto (fun n => g n x) atTop (𝓝 ((0 : Vec ι → ℝ) x)) := by
    apply Eventually.of_forall; intro x
    apply tendsto_const_nhds.congr'
    have h : Tendsto (fun n : ℕ => (n : ℝ) * ‖v‖) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (norm_pos_iff.mpr hv)
    filter_upwards [h.eventually_gt_atTop (1 + ‖x‖)] with n hn
    have hy : x ∉ ball ((n : ℝ) • v) 1 := by
      intro hy
      have hz := dist_triangle ((n : ℝ) • v) x 0
      rw [dist_comm ((n : ℝ) • v) x, dist_zero_right, dist_zero_right, norm_smul,
        Real.norm_natCast] at hz
      exact not_le.mpr hn ((hz.trans (add_le_add_left (mem_ball.mp hy).le ‖x‖)))
    exact (indicator_of_notMem hy F).symm
  have hv := ht hh he
  change Tendsto (fun n : ℕ => ∫ (x : Vec ι), (ball ((n : ℝ) • v) 1).indicator F x)
    atTop (𝓝 (∫ x, (0 : Vec ι → ℝ) x)) at hv
  simpa only [integral_indicator measurableSet_ball, Pi.zero_apply, integral_zero] using hv

/-- Completely real necessity test; in particular the null mode of a PSD matrix still prevents
integrability. -/
lemma posDef_of_integrable_quadratic (A : Gaussian.Table ι) (hA : A.IsSymm) (b : Vec ι) (d : ℝ)
    (h : Integrable (fun z => Real.exp (-quad A z/2 - z ⬝ᵥ b + d)) volume) : A.PosDef := by
  let F (z : Vec ι) := Real.exp (-quad A z/2 - z ⬝ᵥ b + d)
  have hpos z : 0 < F z := Real.exp_pos _
  refine posDef_of_quad_pos hA ?_
  intro v hv; by_contra! hc
  have hz (x : Vec ι) (r : ℝ) : F x + F x ≤ F (r • v + x) + F (r • (-v) + x) := by
    have hr : quad A (r • v) ≤ 0 := by rw [quad_smul]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hc
    have hh : F x * F x ≤ F (r • v + x) * F (r • (-v) + x) := by
      unfold F
      rw [← Real.exp_add, ← Real.exp_add, smul_neg]
      apply Real.exp_monotone
      rw [quad_add hA, quad_add hA, show quad A (-(r • v)) = quad A (r • v) from by
        simp only [quad, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg],
        add_dotProduct, add_dotProduct, neg_dotProduct, neg_dotProduct]
      linarith only [hr]
    have hsq := sq_nonneg (F (r • v+x)-F (r • (-v)+x))
    nlinarith only [hh, hpos x, hpos (r • v + x), hpos (r • (-v) + x), hsq]
  have hI (y : Vec ι) : Integrable (fun x => F (y+x)) volume :=
    ((measurePreserving_add_left volume y).integrable_comp_emb
      (MeasurableEquiv.addLeft y).measurableEmbedding).mpr h
  let R := ∫ x in ball (0 : Vec ι) 1, F x
  have hp : 0 < R := by
    change 0 < ∫ x in ball (0 : Vec ι) 1, F x
    refine (integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) h.integrableOn).mpr ?_
    rw [show support F = univ from eq_univ_of_forall fun x => mem_support.mpr (hpos x).ne',
      Measure.restrict_apply_univ]
    exact measure_ball_pos volume 0 (by norm_num)
  have he y : ∫ x in ball y 1, F x = ∫ x in ball (0 : Vec ι) 1, F (y+x) := by
    have hl := (measurePreserving_add_left volume y).setIntegral_preimage_emb
      (MeasurableEquiv.addLeft y).measurableEmbedding F (ball y 1)
    rw [preimage_add_left_ball, neg_add_cancel] at hl
    exact hl.symm
  have ht : R + R ≤ 0 + (0 : ℝ) := by
    apply ge_of_tendsto' ((vanishes (F:=F) h hv).add (vanishes (F:=F) h (neg_ne_zero.mpr hv)))
    intro n
    rw [he, he ((n : ℝ) • (-v)),
      ← integral_add (hI _ |>.integrableOn) (hI _ |>.integrableOn),
      show R+R = ∫ x in ball (0 : Vec ι) 1, (F x + F x) from
        (integral_add (f:=F) (g:=F) h.integrableOn h.integrableOn).symm]
    exact integral_mono (h.integrableOn.add h.integrableOn) ((hI _).integrableOn.add
      (hI _).integrableOn) (fun x => hz x n)
  linarith only [hp, ht]

end YM.SectorTools.PhysicalGaussianInsertion
