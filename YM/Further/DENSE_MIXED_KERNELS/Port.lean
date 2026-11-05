import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import YM.PCalc.Loop



/-!
# Held group variables for the differentiated kernels

Use the same real orthonormal-color ChartRatio.Patch (has to be the genuine
Haar one, not a quotient or an exponential-chart det with an unspecified
constant). We may narrow the chart a fixed amount; take all held displacement
cutoffs inside this. Product identity even for zero held link count; use with
word-dependent dimensions. g Jacobian added after this step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Lattice RG Wilson Precision Tree
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} (A : ChartRatio G)

/-- One open port throughout work with the kernel. -/
structure Port (A : ChartRatio G) where
  radius : ℝ
  legal : LocalRatio A
  soft : 0 < radius
  inside : radius < A.radius
  left (x : G.Color) : ‖x‖ ≤ radius → G.plog (G.mat (G.lieExp x))=x
  reads (x : G.Color) : ‖x‖ ≤ radius → ContDiffAt ℝ ω G.plog (G.mat (G.lieExp x))
  around : IsOpen (G.lieExp '' Metric.ball 0 radius)



namespace Port
variable {A}
variable (H : Port A)

/-- patch indicator names before the later logarithms. -/
def accepts := Metric.ball (0:G.Color) H.radius
def enters := G.lieExp '' H.accepts

lemma positive_accept {x : G.Color} (h : x ∈ H.accepts) : 0 < A.J x :=
    H.legal.pos _ (Metric.ball_subset_ball H.inside.le h)
lemma ratio (x : G.Color) (h : x∈H.accepts) : G.plog (G.mat (G.lieExp x))=x :=
    H.left x (by simpa [accepts] using (mem_of_mem_of_subset h (show H.accepts⊆Metric.closedBall (0:G.Color) H.radius from Metric.ball_subset_closedBall)))

-- Keep projection totalized only where used. `undo` includes no claim about
-- Smoothness at (or beyond) the boundary.
def undo (x : G.El) := if x∈H.enters then G.plog (G.mat x) else 0
lemma undo_exp {x : G.Color} (h : x∈H.accepts) : H.undo (G.lieExp x)=x :=
    Eq.trans (if_pos (mem_image_of_mem _ h)) (H.ratio x h)
lemma revert {x : G.El} (h : x ∈ H.enters) : H.undo x∈ H.accepts ∧ G.lieExp (H.undo x)=x := by
  obtain ⟨v,hv,rfl⟩ := h; rw [H.undo_exp hv]; exact ⟨hv,rfl⟩

lemma undo_meas : Measurable H.undo := by
  let s := H.enters
  have ho : IsOpen s := H.around
  apply measurable_of_restrict_of_restrict_compl ho.measurableSet
  · refine Continuous.measurable (@ContinuousOn.restrict _ _ _ _ _ _ ?_)
    rintro x ⟨v,hv,rfl⟩
    have hk : G.lieExp v ∈ H.enters := mem_image_of_mem _ hv
    have he : ContinuousAt (fun u => G.plog (G.mat u)) (G.lieExp v) := (H.reads _ (by simpa using! Metric.ball_subset_closedBall hv)).continuousAt.comp G.continuous_mat.continuousAt
    have hx : H.undo =ᶠ[𝓝 (G.lieExp v)] (fun u=>G.plog (G.mat u)) := by
      filter_upwards [ho.mem_nhds hk] with u hu; exact if_pos hu
    exact (he.congr hx.symm).continuousWithinAt
  · have hx : sᶜ.restrict H.undo = fun _ => (0:G.Color) := by
      funext i; exact if_neg (show i.val∉H.enters from i.property)
    rw [hx]; exact measurable_const

lemma pays_port : Measure.map G.lieExp ((volume.restrict H.accepts).withDensity fun x : G.Color => ENNReal.ofReal (A.scale*A.J x)) =
    G.probHaar.restrict H.enters := by
  let f (x : G.Color) := ENNReal.ofReal (A.scale*A.J x)
  let s := Metric.ball (0:G.Color) A.radius
  have he : MeasurableSet H.enters := H.around.measurableSet
  have hv : Measurable G.lieExp := G.lieExp_cont.measurable
  have h : H.accepts ⊆ s := Metric.ball_subset_ball H.inside.le
  have hy : (G.lieExp ⁻¹' H.enters) ∩ s = H.accepts := by
    ext x; constructor
    · rintro ⟨⟨y,hy,hy'⟩,hx⟩; exact (H.legal.inject (h hy) hx hy') ▸ hy
    exact fun hh => ⟨mem_image_of_mem G.lieExp hh,h hh⟩
  have h₁ := Measure.restrict_map (μ:=(volume.restrict s).withDensity f) hv he
  rw [H.legal.actual,Measure.restrict_restrict he, inter_eq_self_of_subset_left (show H.enters ⊆ G.lieExp '' Metric.ball _ _ from image_mono h),restrict_withDensity (hv he),
    Measure.restrict_restrict (hv he), hy] at h₁
  exact h₁.symm

variable {ι : Type*} [Fintype ι]
-- product measures with actual constants.
abbrev Room (_H : Port A) (ι : Type*) := ι → G.Color
abbrev Bound (_H : Port A) (ι : Type*) := ι → G.El

abbrev present := Set.pi Set.univ fun _ : ι => H.accepts
abbrev touch (y : H.Bound ι) : Set (H.Bound ι) := Set.pi Set.univ fun i => {x : G.El | x*(y i)⁻¹ ∈ H.enters}

def stamp (a : H.Room ι) := ∏ i,A.scale*A.J (a i)
def dispatch (y : H.Bound ι) (x : H.Room ι) : H.Bound ι := fun i => G.lieExp (x i) * y i

def hear (y x : H.Bound ι) : H.Room ι := fun i => H.undo (x i*(y i)⁻¹)

omit [Fintype ι] in
lemma enters_when (y : H.Bound ι) {x : H.Room ι} (hx : x ∈ H.present) : H.dispatch y x ∈ H.touch y := by
  intro i hi
  simpa only [mem_setOf_eq,dispatch,mul_inv_cancel_right,enters] using mem_image_of_mem G.lieExp (hx i (mem_univ i))

omit [Fintype ι] in
lemma heard (y : H.Bound ι) {x : H.Room ι} (hx : x ∈ H.present) : H.hear y (H.dispatch y x) = x := by
  ext1 i; unfold hear dispatch; rw [mul_inv_cancel_right]; exact H.undo_exp (hx i (mem_univ i))

omit [Fintype ι] in
lemma heard_mem {y x : H.Bound ι} (hx : x∈H.touch y) : H.hear y x∈ H.present := fun i hi => (H.revert (hx i hi)).1
omit [Fintype ι] in
lemma circles {y x : H.Bound ι} (hx : x∈H.touch y) : H.dispatch y (H.hear y x) = x := by
  ext1 i; unfold dispatch hear; rw [(H.revert (hx i (mem_univ i))).2, inv_mul_cancel_right]
lemma demanded {x : H.Room ι} (hx : x∈H.present) : 0 < H.stamp x := Finset.prod_pos fun i _ => mul_pos H.legal.scale
    (H.positive_accept (hx i (mem_univ i)))

lemma open_present : IsOpen (H.present (ι:=ι)) := isOpen_set_pi (Set.toFinite _) fun _ _ => Metric.isOpen_ball
lemma open_touch (y : H.Bound ι) : IsOpen (H.touch y) := isOpen_set_pi (Set.toFinite _) fun i _ => H.around.preimage (continuous_mul_const (y i)⁻¹)
omit [Fintype ι] in
lemma dispatch_cont (y : H.Bound ι) : Continuous (H.dispatch y) := by unfold dispatch; fun_prop
lemma stamp_meas : Measurable (H.stamp (ι:=ι)) := Finset.measurable_fun_prod _ fun i _ => measurable_const.mul
    (H.legal.borel.comp (measurable_pi_apply i))
omit [Fintype ι] in
lemma hear_joint : Measurable (uncurry (H.hear (ι:=ι))) := by
  refine measurable_pi_lambda _ fun i => H.undo_meas.comp ?_
  unfold Bound; fun_prop

end Port
end YM.Further.DenseMixedKernels
