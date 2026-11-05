import YM.Push.LOOP_COEFFICIENT.MeshMean
import YM.Work.A15
import YM.Work.B04

/-!
# Parameter differentiation at a positive internal strip
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent MeasureTheory Complex Metric
open scoped Topology BigOperators ENNReal ContDiff

lemma zone_ball : zone ⊆ closedBall 0 (2*Real.pi) := by
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right,EuclideanSpace.norm_eq, Real.sqrt_le_iff]; refine ⟨by positivity,?_⟩
  have he (i : Axis) : ‖x i‖ ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (abs_le.mpr ⟨(hx i).1.le,(hx i).2⟩) _
  exact (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => he i)).trans_eq (by simp [Axis]; ring)

instance zone_finite : IsFiniteMeasure (volume.restrict zone) := ⟨by
  simp only [Measure.restrict_apply_univ]; exact (measure_mono zone_ball).trans_lt (isCompact_closedBall _ _).measure_lt_top⟩

lemma radians_cont : Continuous radians := by unfold radians; fun_prop
lemma radians_strip (x : E4) {η : ℝ} (hη : 0 < η) : radians x ∈ strip η := by intro i; simpa [radians]

variable {X F : Type} [NormedAddCommGroup X] [NormedAddCommGroup F]
    {u v : Momentum → F} {η η' : ℝ}
lemma zone_integrable (h : ∀ q : E4, ContinuousAt u (radians q)) : IntegrableOn (fun q => u (radians q)) zone :=
  (ContinuousOn.integrableOn_compact (isCompact_closedBall ..) (((continuous_iff_continuousAt.mpr
    fun x => (h x).comp radians_cont.continuousAt)).continuousOn)).mono_set zone_ball

lemma zone_congr [NormedSpace ℝ F] (h : ∀ q ∈ zone, u (radians q) = v (radians q)) : boxMean u = boxMean v :=
  congr_arg (normalize4 • ·) (integral_congr_ae ((ae_restrict_mem zone_measurable).mono h))

lemma normalize_correct : normalize4 * volume.real zone = 1 := by
  have hv : Vane (α:=Axis) (fun _ => 1) 1 := ⟨by linarith,fun _ _ => differentiableAt_const _,fun _ _ _ => rfl⟩
  have hh := mean_market hv
  have he : market (fun (_:Momentum) => 1) 0 0 = 1 := by
    rw [market,UnitAddTorus.mFourierCoeff]; simp only [neg_zero, UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,one_smul,veils]
    change (∫ _ : UnitAddTorus Axis,(1:ℂ) ∂globe Axis) = 1; simp
  rw [he, boxMean, setIntegral_const] at hh
  simpa only [Complex.real_smul,Complex.mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,one_re,mul_one] using! congr_arg Complex.re hh.symm

lemma boxMean_norm [NormedSpace ℝ F] {b : ℝ} (h : ∀ q∈zone, ‖u (radians q)‖ ≤ b) : ‖boxMean u‖ ≤ b := by
  unfold boxMean; rw [norm_smul,Real.norm_eq_abs,abs_of_pos normalize_pos]
  calc
    _ ≤ normalize4 * (b * volume.real zone) := mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const (by simpa using zone_finite.measure_univ_lt_top) h) normalize_pos.le
    _ = b := by rw [mul_left_comm, normalize_correct,mul_one]

section calculus
variable [NormedSpace ℂ X] [FiniteDimensional ℂ X] [NormedSpace ℂ F] [NormedSpace ℝ F] [SMulCommClass ℂ ℝ F]
variable {u : X → Momentum → F}

omit [FiniteDimensional ℂ X] [NormedSpace ℝ F] [SMulCommClass ℂ ℝ F] in
private lemma fd {x : X} {q} (hu : ContDiffAt ℂ ω (Function.uncurry u) (x,q)) :
    ContDiffAt ℂ ω (fun z : X × Momentum => fderiv ℂ (fun p => u p z.2) z.1) (x,q) :=
  ContDiffAt.fderiv (f:=fun z : X × Momentum => fun p => u p z.2) (g:=Prod.fst)
    (hu.comp (f := fun w : (X×Momentum) × X => (w.2,w.1.2)) ((x,q),x) (by fun_prop)) contDiffAt_fst (by simp)

omit [FiniteDimensional ℂ X] [NormedSpace ℝ F] [SMulCommClass ℂ ℝ F] in
private lemma fd_apply (x : X) (q) (hu : ContDiffAt ℂ ω (Function.uncurry u) (x,q)) :
    HasFDerivAt (fun x => u x q) (fderiv ℂ (fun x => u x q) x) x :=
  ((hu.comp (f:=fun z => (z,q)) x (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)).hasFDerivAt

lemma boxMean_derivative {S : Set X} {p : X} (hS : S ∈ 𝓝 p)
    (h : ∀ x∈ S, ∀ k : E4, ContDiffAt ℂ ω (Function.uncurry u) (x, radians k)) :
    HasFDerivAt (fun x => boxMean (u x)) (boxMean (fun q => fderiv ℂ (fun x => u x q) p)) p := by
  let D x q := fderiv ℂ (fun x => u x q) x
  obtain ⟨r,hr,hR⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hS
  let R := closedBall p r
  letI := FiniteDimensional.proper ℂ X
  let μ := volume.restrict zone
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p r).prod (isCompact_closedBall 0 (2*Real.pi))).bddAbove_image
    (f:=fun z : X × E4 => ‖D z.1 (radians z.2)‖) (fun x hx => (((fd (h x.1 (hR hx.1) x.2)).continuousAt.comp
      (f:=fun z : X × E4 => (z.1,radians z.2)) (continuousAt_fst.prodMk (radians_cont.continuousAt.comp continuousAt_snd))).norm.continuousWithinAt))
  have he x (hx : x ∈ S) : Integrable (fun q => u x (radians q)) μ := zone_integrable (fun q => (h x hx q).continuousAt.comp (f:=fun q => (x,q)) (continuousAt_const.prodMk continuousAt_id))
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜:=ℂ) (F':=fun x q => D x (radians q)) (μ:=μ)
    (Metric.closedBall_mem_nhds p hr) (eventually_of_mem hS fun x hx => (he x hx).aestronglyMeasurable)
    (he p (mem_of_mem_nhds hS)) (zone_integrable (u:=D p) (fun q => (fd (h p (mem_of_mem_nhds hS) q)).continuousAt.comp
      (f:=fun q => (p,q)) (continuousAt_const.prodMk continuousAt_id))).aestronglyMeasurable ((ae_restrict_mem zone_measurable).mono
        fun k hk x hx => (show _ ≤ C from hC ⟨(x,k),⟨hx, zone_ball hk⟩,rfl⟩)) (integrable_const C)
    ((ae_restrict_mem zone_measurable).mono fun k _ x hx => fd_apply x _ (h x (hR hx) k))
  exact hd.const_smul _





lemma boxMean_smooth [FiniteDimensional ℂ F] {S : Set X} {p : X} (hS : S ∈ 𝓝 p)
    (h : ∀ x∈ S, ∀ k : E4, ContDiffAt ℂ ω (Function.uncurry u) (x, radians k)) : ContDiffAt ℂ ω (fun x => boxMean (u x)) p := by
  haveI := FiniteDimensional.complete ℂ F
  exact (PolyDisc.finiteD _ ((eventually_eventually_nhds.mpr hS).mono (fun _ hx => (boxMean_derivative hx h).differentiableAt))).contDiffAt
end calculus
end YM.Push.Loops
