import YM.Further.DENSE_MIXED_KERNELS.Port

/-!
# Change of variables behind FKer

Use positive real g. Product link probability Haar (frozen link coordinates
upstream also probability), relative to the actual density convention. No
smallness statement needed for counting here. The ball used for the larger
patch surrounds every numerical support of the protectors; no derivative
of even its indicator in an integral is needed. Don't assume these hypotheses
with a default patch already dropped unless some other protector paid for it.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

section transport
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X→Y} {j k : X → ℝ≥0∞}

lemma replace (h : Measurable f) {u : Y → ℝ≥0∞} (hh : Measurable u) :
    (Measure.map f μ).withDensity u = Measure.map f (μ.withDensity (u ∘ f)) := by
  refine Measure.ext_of_lintegral _ (fun φ hφ => ?_)
  rw [lintegral_withDensity_eq_lintegral_mul _ hh hφ, lintegral_map (hh.mul hφ) h, lintegral_map hφ h,
    lintegral_withDensity_eq_lintegral_mul _ (hh.comp h) (show Measurable (fun x => φ (f x)) from hφ.comp h)]; rfl

/-- Rearrange densities for a held-coordinate scope without dropping a patch
or asserting total mass 1 in that scope. -/
lemma pump {ν : Measure Y} {u : Y → ℝ≥0∞} (h : Measurable f) (hy : Measurable u) (hj : Measurable j)
    (hm : Measure.map f (μ.withDensity j)=ν) (he : k=ᵐ[μ] j*(u∘f)) : Measure.map f (μ.withDensity k)=ν.withDensity u := by
  rw [← hm,replace h hy, withDensity_congr_ae he,withDensity_mul μ hj (hy.comp h)]
end transport
namespace Port
variable {G : Gauge} {A : ChartRatio G} (H : Port A) {ι : Type*} [Fintype ι]

private lemma deck_apply {ι E : Type*} [MeasurableSpace E] [Fintype ι] {μ : ι → Measure E} [∀ i, SigmaFinite (μ i)]
    (f : ι → E → ℝ) (h : ∀ i,Integrable (f i) (μ i)) (hv : ∀ i,0 ≤ᵐ[μ i] f i) :
    Measure.pi (fun i => (μ i).withDensity fun x => ENNReal.ofReal (f i x)) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  have hi (i : ι) := isFiniteMeasure_withDensity_ofReal (h i).2
  apply Measure.pi_eq
  intro s hs
  let M i := (μ i).restrict (s i)
  have hM : ∀ i,SigmaFinite (M i) := fun i => by unfold M; infer_instance
  have he i : Integrable (f i) (M i) := (h i).restrict
  have hg i : 0 ≤ᵐ[M i] f i := ae_restrict_of_ae (hv i)
  have hZ : 0 ≤ᵐ[Measure.pi M] fun x => ∏ i, f i (x i) := by
    filter_upwards [Filter.eventually_all.mpr fun i : ι => Measure.tendsto_eval_ae_ae (μ:=M) |>.eventually (hg i)] with x hx
    exact Finset.prod_nonneg fun i (_:i∈Finset.univ) => hx i
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi, ← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod he) hZ, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
      (fun i _ => integral_nonneg_of_ae (hg i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← ofReal_integral_eq_lintegral_ofReal (he i) (hg i)]

abbrev heldLaw := Measure.pi fun _ : ι => G.probHaar

lemma purse (w : H.Bound ι) :
    Measure.map (H.dispatch w) ((volume.restrict H.present).withDensity (fun a : H.Room ι => ENNReal.ofReal (H.stamp a))) =
      heldLaw.restrict (H.touch w) := by
  let M := Metric.closedBall (0:G.Color) H.radius
  have hu : Integrable (fun x : G.Color => A.scale*A.J x) (volume.restrict H.accepts) := by
    have hg : ContinuousOn A.J M := fun x hx => (H.legal.germ _ (Metric.closedBall_subset_ball H.inside hx)).continuousAt.continuousWithinAt
    exact (((continuousOn_const (c:=A.scale)).mul hg).integrableOn_compact (ProperSpace.isCompact_closedBall ..)).mono_set (by exact Metric.ball_subset_closedBall)
  let m := (volume.restrict H.accepts).withDensity (fun x => ENNReal.ofReal (A.scale*A.J x))
  have h : MeasurePreserving G.lieExp m (G.probHaar.restrict H.enters) := ⟨G.lieExp_cont.measurable,H.pays_port⟩
  let t i := {x : G.El | x*(w i)⁻¹∈ H.enters}
  have hh i : MeasurePreserving (fun x=>x*w i) (G.probHaar.restrict H.enters) (G.probHaar.restrict (t i)) := by
    have he := (measurePreserving_mul_right G.probHaar (w i)).restrict_preimage (show MeasurableSet (t i) from (measurable_mul_const _ H.around.measurableSet))
    rwa [show (fun x => x*w i) ⁻¹' t i = H.enters by ext; simp [t]] at he
  unfold stamp present touch heldLaw
  rw [volume_pi,Measure.restrict_pi_pi, Measure.restrict_pi_pi,←deck_apply (μ:=fun _ => volume.restrict H.accepts) (ι:=ι) (fun _ x => A.scale * A.J x) (fun _ => hu) (fun _ => ?_)]
  · exact (measurePreserving_pi (fun _ => m) (fun i => G.probHaar.restrict (t i)) fun i : ι => (hh i).comp h).map_eq
  · filter_upwards [ae_restrict_mem (show MeasurableSet H.accepts from Metric.isOpen_ball.measurableSet)] with x hx
    exact mul_nonneg H.legal.scale.le (H.positive_accept hx).le

end Port
end YM.Further.DenseMixedKernels
