import YM.Analysis.MomentPD

/-!
# Compression of labels over compact variables, Schur positivity
-/
set_option autoImplicit false
noncomputable section
namespace YM.Analysis
open Filter Function MeasureTheory
open scoped Topology BigOperators ComplexOrder
variable {X A B : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

namespace Quad

def average (Q : Quad X) (g : X → X → ℂ) := ∑ i, (Q.mass μ i : ℂ) * ∑ j, (Q.mass μ j : ℂ) *
  g (Q.tag i) (Q.tag j)

theorem approx {F : X → X → ℂ} (h : Continuous (fun z : X × X => F z.1 z.2)) :
    Tendsto (fun i => average μ (shrink X i) F) atTop (𝓝 (∫ x, ∫ y, F x y ∂μ ∂μ)) := by
  classical
  let g (Q : Quad X) := fun z : X × X => F (Q.map z.1) (Q.map z.2)
  obtain ⟨c,hc⟩ := h.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  have hs (Q : Quad X) : Measurable (g Q) := h.measurable.comp
    ((Q.meas_map.comp measurable_fst).prodMk (Q.meas_map.comp measurable_snd))
  have he (Q : Quad X) (x) : ‖g Q x‖ ≤ c := hc (Q.map x.1, Q.map x.2)
  have hx (Q : Quad X) : (∫ x, g Q x ∂(μ.prod μ)) = average μ Q F := by
    rw [integral_prod _ (Integrable.of_bound (hs Q).aestronglyMeasurable c
      (Eventually.of_forall fun x => he Q x))]
    change (∫ x, ∫ y, F (Q.map x) (Q.map y) ∂μ ∂μ) = _
    rw [Q.count μ (fun x => ∫ y, F x (Q.map y) ∂μ)]
    dsimp only [average]
    simp_rw [Q.count μ, Complex.real_smul]
  simp_rw [← hx]
  rw [← integral_prod (fun z : X × X => F z.1 z.2) (h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  refine tendsto_integral_of_dominated_convergence (fun _ => c) (fun i => (hs _).aestronglyMeasurable)
    (integrable_const _) (fun i => Eventually.of_forall fun x => he _ _) (Eventually.of_forall fun x => ?_)
  exact h.continuousAt.tendsto.comp ((along x.1).prodMk_nhds (along x.2))
end Quad

namespace NNKernel

/-- Form new labels by integrating over independent random variables, one on each side. -/
theorem accumulate {g : B → X → A} {K : A → A → ℂ} (H : NNKernel K)
    (he : ∀ b c : B, Continuous fun p : X × X => K (g b p.1) (g c p.2)) :
    NNKernel (fun b c => ∫ i : X, ∫ j : X, K (g b i) (g c j) ∂μ ∂μ) := by
  let G (Q : Quad X) (b c : B) := Quad.average μ Q fun i j => K (g b i) (g c j)
  have hh (Q : Quad X) : NNKernel (G Q) := by
    apply criterion
    · intro b c
      unfold G Quad.average
      simp only [star_sum,Finset.mul_sum, star_mul',Complex.star_def, Complex.conj_ofReal]
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl
      intro i _; apply Finset.sum_congr rfl; intro j _
      have hs := H.swaps (g b (Q.tag i)) (g c (Q.tag j))
      simp only [Complex.star_def] at hs
      rw [hs]; ring
    intro m f r
    let w (i : Fin Q.size) := (Q.mass μ i : ℂ)
    have hp := H.positivity (I := Fin m × Fin Q.size) (fun i => g (f i.1) (Q.tag i.2)) (fun i => r i.1 * w i.2)
    simp only [Fintype.sum_prod_type] at hp
    unfold G Quad.average
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine le_trans hp (le_of_eq ?_)
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl
    intro k _; apply Finset.sum_congr rfl
    intro i _; apply Finset.sum_congr rfl; intro l h
    simp [w]; ring
  exact closed (fun i => G (Quad.shrink X i)) (fun i => hh _) (fun x y => Quad.approx μ (he x y))
end NNKernel
end YM.Analysis
