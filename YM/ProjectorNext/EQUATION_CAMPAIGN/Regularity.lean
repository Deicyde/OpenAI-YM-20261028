import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral




set_option warningAsError false

/-!
Real smoothness under integrations here. For later use with a channel/tag kernel even
allow a measurable (not smooth) family of parameters, provided it ranges in a compact
and the sample weight is integrable. No radii or estimates through iteration claimed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equations

open MeasureTheory Set Filter Topology
open scoped ContDiff

section Weighted

-- keep weighted-scalar versions for complex coefficients too
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {𝕜 : Type*} [RCLike 𝕜]
    {Y X Z : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [NormedSpace ℝ Z] [SMulCommClass 𝕜 ℝ Z]
    {W : α → 𝕜} {F : α → Y} {f : X × Y → Z} {C : Set Y}

omit [NormedSpace ℝ Y] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedSpace ℝ Z] [SMulCommClass 𝕜 ℝ Z] in
lemma compact_weight (hw : Integrable W μ) (hF : AEStronglyMeasurable F μ)
    (hC : IsCompact C) (hc : ∀ᵐ i ∂μ,F i ∈ C) (h : Continuous f) (x : X) :
    Integrable (fun i => W i • f (x,F i)) μ := by
  let g := fun y : Y => f (x,y)
  have hg : Continuous g := h.comp (by fun_prop)
  obtain ⟨M,hM⟩ := (hC.image hg.norm).bddAbove
  refine (hw.norm.mul_const M).mono'
    (hw.aestronglyMeasurable.smul (hg.comp_aestronglyMeasurable hF)) ?_
  filter_upwards [hc] with i hi
  rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hM ⟨_,hi,rfl⟩) (norm_nonneg _)

omit [FiniteDimensional ℝ X] in
private lemma partial_smooth (h : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : X × Y => fderiv ℝ (fun x => f (x,p.2)) p.1) := by
  let g (p : X × Y) (x : X) := f (x,p.2)
  exact (ContDiff.fderiv (f:=g) (g:=Prod.fst) (n:=∞)
    (h.comp (f:=fun p : (X × Y) × X => (p.2,p.1.2)) (by fun_prop)) contDiff_fst (by simp))

omit [SMulCommClass 𝕜 ℝ Z] in
private lemma at_point (hw : Integrable W μ) (hF : AEStronglyMeasurable F μ)
    (hC : IsCompact C) (hc : ∀ᵐ i ∂μ,F i∈C) (h : ContDiff ℝ ∞ f) (x : X) :
    HasFDerivAt (fun v => ∫ i, W i • f (v,F i) ∂μ)
      (∫ i, W i • fderiv ℝ (fun v => f (v,F i)) x ∂μ) x := by
  let p (q : X × Y) := fderiv ℝ (fun v => f (v,q.2)) q.1
  have hp : Continuous p := (partial_smooth h).continuous
  obtain ⟨M,hM⟩ := (((isCompact_closedBall x 1).prod hC).image hp.norm).bddAbove
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun x i => W i • p (x,F i))
      (Metric.closedBall_mem_nhds x zero_lt_one)
      (Eventually.of_forall fun _ => (compact_weight hw hF hC hc h.continuous _).aestronglyMeasurable)
      (compact_weight hw hF hC hc h.continuous _)
      (compact_weight hw hF hC hc hp x |>.aestronglyMeasurable) ?_ (hw.norm.mul_const M) ?_
  · filter_upwards [hc] with i hi x hx
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hM ⟨(x,F i),⟨hx,hi⟩,rfl⟩) (norm_nonneg _)
  filter_upwards with i x hx
  exact ((h.comp (f:=fun v : X => (v,F i)) (by fun_prop)).differentiable (by simp) x |>.hasFDerivAt).const_smul _

/-- Integrating in labelled data at compact ranges gives genuine smooth dependence. -/
theorem contDiff_weighted [CompleteSpace Z]
    (hw : Integrable W μ) (hF : AEStronglyMeasurable F μ)
    (hC : IsCompact C) (hc : ∀ᵐ i ∂μ,F i∈C) (h : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => ∫ i, W i • f (x,F i) ∂μ) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing Z with
  | zero =>
    have hs : Differentiable ℝ (fun x => ∫ i,W i • f (x,F i) ∂μ) :=
      fun x => (at_point hw hF hC hc h x).differentiableAt
    simpa using hs.continuous
  | succ n ih =>
    push_cast; rw [contDiff_succ_iff_fderiv]; have he x := at_point hw hF hC hc h x
    refine ⟨fun x => (he x).differentiableAt,by simp,?_⟩
    rw [funext fun x => (he x).fderiv]
    exact ih (partial_smooth h)
end Weighted

open scoped Interval

section Unit
variable {X Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]


end Unit
end YM.ProjectorNext.Equations
