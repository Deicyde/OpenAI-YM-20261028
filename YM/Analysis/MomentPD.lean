import YM.Analysis.Quadrature

/-!
# Integrating a nonnegative definite kernel

Weights can be bounded measurable, not sampled. Use Product `ν.prod`.
Works on any compact metric X incl empty/dim0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Analysis.NNKernel
open Filter Function Set Metric MeasureTheory TopologicalSpace
open scoped ComplexOrder Topology BigOperators

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
variable {K : X → X → ℂ} (μ : Measure X) [IsFiniteMeasure μ]

lemma integrated (H : NNKernel K) (h : Continuous (fun x : X × X => K x.1 x.2)) {f : X → ℂ}
    (hf : Measurable f) {C : ℝ} (hw : ∀ x, ‖f x‖ ≤ C) :
    0 ≤ ∫ x : X × X, K x.1 x.2 * star (f x.1) * f x.2 ∂(μ.prod μ) := by
  classical
  let block (Q : Quad X) := fun x : X × X => K (Q.map x.1) (Q.map x.2) * star (f x.1) * f x.2
  have he (Q : Quad X) : 0 ≤ ∫ x, block Q x ∂(μ.prod μ) := by
    let A i := (Q.tile i).indicator f
    have hi : ∀ i, Integrable (A i) μ := fun i =>
      (Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hw)).indicator (Q.tile_meas _)
    let Φ (i : Fin Q.size × Fin Q.size) (x : X × X) := K (Q.tag i.1) (Q.tag i.2) *
       (star (A i.1 x.1) * A i.2 x.2)
    have hj (i : Fin Q.size × Fin Q.size) : Integrable (Φ i) (μ.prod μ) := by
      refine Integrable.const_mul ?_ _; exact (((starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap).integrable_comp (hi i.1)).mul_prod (hi i.2)
    have hv : block Q = fun x => ∑ i, Φ i x := by
      ext1 v
      rw [Finset.sum_eq_single_of_mem (Q.slice v.1, Q.slice v.2) (Finset.mem_univ _)]
      · simp [block,Φ,A,Quad.map,Quad.tile, mul_assoc]
      rintro ⟨i,j⟩ hi h'
      simp only [Ne, Prod.mk.injEq, not_and_or] at h'
      rcases h' with h'|h' <;> simp [Φ,A,Quad.tile, Ne.symm h']
    rw [hv, integral_finsetSum _ (fun i _ => hj i)]
    have hI (i : Fin Q.size × Fin Q.size) : (∫ x, Φ i x ∂(μ.prod μ)) = star (∫ x, A i.1 x ∂μ) *
        K (Q.tag i.1) (Q.tag i.2) * ∫ x, A i.2 x ∂μ := by
      simp only [Φ, integral_const_mul]
      rw [integral_prod_mul (fun x => star (A i.1 x)) (A i.2)]
      simp only [Complex.star_def,integral_conj]; ring
    simp_rw [hI,Fintype.sum_prod_type]; exact H.positivity Q.tag _
  obtain ⟨D,hD⟩ := h.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  apply ge_of_tendsto (f := fun i => ∫ v, block (Quad.shrink X i) v ∂(μ.prod μ)) (x := atTop) _
    (Eventually.of_forall fun i => he _)
  refine tendsto_integral_of_dominated_convergence (fun _ => D*C*C) ?_ (integrable_const _) ?_ ?_
  · intro i
    have hM := (Quad.shrink X i).meas_map
    refine (((h.measurable.comp ((hM.comp measurable_fst).prodMk (hM.comp measurable_snd))).mul
      ((continuous_star (R := ℂ)).measurable.comp (hf.comp measurable_fst))).mul (hf.comp measurable_snd)).aestronglyMeasurable
  · intro i; refine Eventually.of_forall fun x => ?_
    have hp := norm_nonneg _ |>.trans (hw x.2)
    have hr := norm_nonneg _ |>.trans (hD (x.1,x.2))
    unfold block
    rw [norm_mul,norm_mul,norm_star]
    exact mul_le_mul (mul_le_mul (hD (_, _)) (hw _) (norm_nonneg _) hr) (hw x.2) (norm_nonneg _) (mul_nonneg hr hp)
  refine Eventually.of_forall fun x => ?_
  exact ((h.continuousAt.tendsto.comp ((Quad.along x.1).prodMk_nhds (Quad.along x.2))).mul_const
     (star (f x.1))).mul_const _
end YM.Analysis.NNKernel
