import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Ac.Table
import YM.Planned.PRIMARY_INTEGRAL_295.Ripple
import YM.Pressure.Seeds

/-! # Integration at EVERY actual joint θ and all varying nontree registers

σ-sum weighted Gaussians handles variation in marginal dimension, no
adding channels or independent choices. Cannot split intersections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Twines
open Function Filter Set Metric MeasureTheory ProbabilityTheory  Ripple
open scoped Topology BigOperators ENNReal NNReal ContDiff
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
variable (M : ∀ i,Measure (Ω i)) (φ : ι→ℝ≥0)

-- σ spaces. Borel-fiber readability.
def dial := ∑ i, φ i • Measure.map (Sigma.mk i) (M i)
omit [Fintype ι] in
lemma slice (X : Set (Sigma Ω)) : MeasurableSet X ↔ ∀ i, MeasurableSet ((Sigma.mk i) ⁻¹' X) :=
    MeasurableSpace.measurableSet_iInf
omit [Fintype ι] in
lemma mirror (i : ι) : MeasurableEmbedding (Sigma.mk (β:=Ω) i) := by
  classical
  have he (i) : Injective (Sigma.mk (β:=Ω) i):=fun x y h=>eq_of_heq ((Sigma.mk.inj h).2)
  refine ⟨he i,fun X hX=> (slice _).mp hX i,fun X hX=> (slice _).mpr fun j=>?_⟩
  by_cases hh : j=i
  · subst j; simpa [Set.preimage_image_eq X (he i)] using hX
  rw [show (Sigma.mk j ⁻¹' (Sigma.mk i '' X))=∅ from Set.eq_empty_of_forall_notMem (fun k => by
    rintro ⟨v, hv,hr⟩; exact hh (congr_arg Sigma.fst hr).symm)]; exact MeasurableSet.empty

lemma along {p : Sigma Ω→Prop} (h : ∀ i, ∀ᵐ x ∂M i,p ⟨i,x⟩) : ∀ᵐ x∂dial M φ,p x := by
  unfold dial; rw [ae_finsetSum_measure_iff]; intro i _
  exact Measure.ae_smul_measure ((mirror _).ae_map_iff.mpr (h i)) (φ i)



section Vital
variable {E : Type*} [NormedAddCommGroup E] (f : Sigma Ω→E)
omit [Fintype ι] in
private lemma slips (h : ∀ i,Integrable (f ∘ Sigma.mk i) (M i)) (i:ι) : Integrable f (φ i • Measure.map (Sigma.mk i) (M i)) :=
    ((mirror i).integrable_map_iff.mpr (h i)).smul_measure_nnreal

lemma bust (h : ∀ i,Integrable (f ∘ Sigma.mk i) (M i)) : Integrable f (dial M φ) :=
    integrable_finsetSum_measure.mpr (fun i _=> slips M φ f h i)
variable [NormedSpace ℝ E]
lemma blend (h : ∀ i,Integrable (f ∘ Sigma.mk i) (M i)) :
    (∫ x,f x ∂dial M φ)=∑ i, (φ i:ℝ) • (∫ z,f ⟨i,z⟩ ∂M i) := by
  classical
  unfold dial; rw [integral_finsetSum_measure (fun i _=>slips M φ f h i)]; refine Finset.sum_congr rfl (fun i _=> ?_)
  rw [integral_smul_nnreal_measure,(mirror i).integral_map]; rfl
end Vital

lemma weighed {C : ℝ} (h : ∑ i,φ i=1) (f : Sigma Ω→ℝ) (hi : ∀ i, Integrable (f ∘ Sigma.mk i) (M i))
    (he : ∀ i, (∫ z,f ⟨i,z⟩ ∂M i) ≤ C) : (∫ z, f z ∂dial M φ) ≤ C := by
  classical
  rw [blend _ _ f hi]; apply (Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (he i) (φ i).coe_nonneg)).trans
  rw [← Finset.sum_mul,← NNReal.coe_sum,h,NNReal.coe_one,one_mul]

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {X : Sigma Ω→E→F} {x:E} {k:ℕ}

-- combine demand over whole chart. σ-finite or not; actual μ chamber.
lemma more (h : ∀ i, Regales (X ∘ Sigma.mk i) (M i) k x) : Regales X (dial M φ) k x := by
  classical
  choose S hS H using h
  let T:= ⋂ i,S i
  have hT : IsOpen T:=isOpen_iInter_of_finite (fun i=> (H i).room)
  have he (i:ι) : T ⊆ S i := iInter_subset ..
  refine ⟨T,mem_iInter.mpr hS,hT,?_,fun n hn y hy=>?_,fun n hn=>?_⟩
  · exact along M φ (fun i=> (H i).contour.mono fun z hz y hy=> hz y (he i hy))
  · exact (bust M φ (report X n y) (fun i=> (H i).serves (he i hy) hn)).aestronglyMeasurable
  choose b hb Hb using fun i=> (H i).volume n hn
  refine ⟨fun z => b z.1 z.2, bust M φ (fun z => b z.1 z.2) hb, ?_⟩
  exact along M φ fun i=> (Hb i).mono fun z hz y hy=> hz y (he i hy)
end
end YM.Planned.PrimaryIntegral295.Twines
