import YM.Slice.Gate

/-!
# Proof of seam reflection positivity for actual Wilson lattice

Works for all nonnegative beta. Integrals justified before domination.
Never replace crossing links in a probe: it must be measurable, strict.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open Function Set Filter MeasureTheory
open Lattice Wilson Cells Analysis
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder ComplexConjugate
variable {n : Side} {G : Gauge} (C : Cut n) (β : ℝ)

private lemma area_cont (u : Posts C G) : Continuous (area C β u) := by
  unfold area
  refine continuous_finsetProd _ ?_; intro i _
  have he : Continuous (reader C u) := by
    have hv := (continuous_follow C (G := G)).comp (show Continuous fun v : Open C G => ((u, (1 : Doors C G)), v, v) from by fun_prop)
    exact hv
  have hx (i : Per n) : Continuous (fun p : Open C G => reader C u p i) := (continuous_apply i).comp he
  have H := (weight_cont C.pos (n := n) (G := G) β).comp (show Continuous
    (fun p : Open C G => ((reader C u p i).1,(reader C u p (i.val+1)).1,(reader C u p i).2)) from
    (hx _).fst.prodMk ((hx _).fst.prodMk (hx _).snd))
  exact H

private def factors (F : Config G n → ℂ) (u : Posts C G) (x : Open C G) :=
  (area C β u x : ℂ) * F (chain C.pos (reader C u x))

private lemma fm (F : Config G n → ℂ) (H : Interior C.sector F) (u : Posts C G) : Measurable (factors C β F u) := by
  refine ((Complex.continuous_ofReal.comp (area_cont C β u)).measurable).mul (H.borel.comp ?_)
  apply Continuous.measurable
  apply (chain_cont C.pos).comp
  exact (continuous_follow C).comp (show Continuous fun v : Open C G => ((u,(1 : Doors C G)),v,v) from by fun_prop)

private def terms (F : Config G n → ℂ) (i : Config G n) := F i * star (F (C.pullC G i))
private def examines (F : Config G n → ℂ) (p : Dwelling C G) : ℂ :=
  let v := chain C.pos (follow C p)
  (bare β v : ℂ)*terms C F v

private lemma tall (F : Config G n → ℂ) (H : Interior C.sector F) {μ : Measure (Config G n)} [IsFiniteMeasure μ] :
    Integrable (terms C F) μ := by
  obtain ⟨c,hc⟩ := H.cost
  refine Integrable.of_bound (f := (terms C F)) ?_ (c*c) ?_
  · exact (H.borel.mul ((continuous_star (R := ℂ)).measurable.comp (H.borel.comp (continuous_pull _ _).measurable))).aestronglyMeasurable
  exact Eventually.of_forall fun x => calc
    _ ≤ _ := norm_mul_le ..
    _ ≤ _ := mul_le_mul (hc _) ((norm_star _).trans_le (hc _)) (norm_nonneg _) ((norm_nonneg _).trans (hc x))

private lemma readers (F : Config G n → ℂ) (H : Interior C.sector F) (P : Dwelling C G) :
    examines C β F P = (rim C β P : ℂ)*factors C β F P.1.1 P.2.1 * star (factors C β F P.1.1 P.2.2) := by
  unfold examines terms factors
  dsimp only
  rw [includes, H.localSites _ _ (first_eye C P),H.localSites _ _ (second_eye C P)]; simp; ring

private lemma link_positive (F : Config G n → ℂ) (H : Interior C.sector F) (hβ : 0 ≤ β) (u : Posts C G) :
    0 ≤ ∫ v : Open C G × Open C G, (∫ d : Doors C G, examines C β F ((u,d),v) ∂doorM G C) ∂((fieldM G C).prod (fieldM G C)) := by
  simp_rw [readers C β F H, integral_mul_const];
  let f := factors C β F u
  have h : ∃ c : ℝ, ∀ x, ‖star (f x)‖ ≤ c := by
    obtain ⟨D,hD⟩ := (area_cont C β u).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
    obtain ⟨E,hE⟩ := H.cost
    refine ⟨D*E,fun x => ?_⟩
    unfold f factors; rw [norm_star,norm_mul,Complex.norm_real]
    exact mul_le_mul (hD x) (hE _) (norm_nonneg _) ((norm_nonneg (area C β u x)).trans (hD _))
  obtain ⟨c,hc⟩ := h
  haveI : @BorelSpace (Open C G) (MetricSpace.toPseudoMetricSpace (α := Open C G)).toUniformSpace.toTopologicalSpace (inferInstance : MeasurableSpace _) := instBorelSpaceOpen C
  haveI : @SecondCountableTopology (Open C G) (MetricSpace.toPseudoMetricSpace (α := Open C G)).toUniformSpace.toTopologicalSpace := instSecondCountableTopologyOpen _
  haveI : @CompactSpace (Open C G) (MetricSpace.toPseudoMetricSpace (α := Open C G)).toUniformSpace.toTopologicalSpace := (inferInstance : CompactSpace (Open C G))
  have hv := NNKernel.integrated (X := Open C G) (fieldM G C) (portPos C β u hβ) (portContinuous C β u)
    (f := fun i => star (f i)) ((continuous_star (R := ℂ)).measurable.comp (fm C β F H u)) hc
  simp only [star_star] at hv; exact hv

-- if need Fubini exchange a.e. enough.
private lemma insidePos (F : Config G n → ℂ) (H : Interior C.sector F) (hβ : 0 ≤ β)
    (hv : Integrable (examines C β F) (dwellM G C)) :
    0 ≤ ∫ x, examines C β F x ∂dwellM G C := by
  unfold dwellM at hv ⊢; rw [integral_prod _ hv]
  let m := ((fieldM G C).prod (fieldM G C))
  let f := examines C β F
  have hi : Integrable (fun y : Posts C G × Doors C G => ∫ x, f (y,x) ∂m) ((postM G C).prod (doorM G C)) :=
    Integrable.integral_prod_left hv
  change 0 ≤ ∫ y : Posts C G × Doors C G, (∫ x, f (y,x) ∂m) ∂((postM G C).prod (doorM G C))
  rw [integral_prod _ hi]
  -- need reorder at μ-almost every post.
  apply integral_nonneg_of_ae
  have hj : Integrable (fun x : Posts C G × Doors C G × Open C G × Open C G => f ((x.1,x.2.1),x.2.2))
      ((postM G C).prod ((doorM G C).prod m)) := by
    have hμ := measurePreserving_prodAssoc (postM G C) (doorM G C) m
    exact hμ.symm.integrable_comp_of_integrable hv
  have hL : ∀ᵐ u ∂postM G C, Integrable (fun x : Doors C G × Open C G × Open C G => f ((u,x.1),x.2)) ((doorM G C).prod m) :=
    hj.prod_right_ae
  filter_upwards [hL] with u hu
  rw [integral_integral_swap hu]; exact link_positive C β F H hβ u

theorem reflected_positive (hβ : 0 ≤ β) : Positive G β C := by
  intro F H
  have HT : Integrable (fun v => (bare β v : ℂ)*terms C F v) (prior G n) := by
    obtain ⟨c,hc⟩ := (bare_cont (G := G) (n := n) β).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
    apply Integrable.bdd_mul (tall C F H)
      (Complex.continuous_ofReal.measurable.comp (bare_cont β).measurable).aestronglyMeasurable
    exact Eventually.of_forall fun x => show ‖(bare β x : ℂ)‖ ≤ c from by simp only [Complex.norm_real]; exact hc _
  change 0 ≤ moment β (terms C F)
  rw [moment_formula β (terms C F) (tall C F H)]
  have hm (f : Config G n → ℂ) (h' : Integrable f (prior G n)) :
      (∫ p, f (chain C.pos (follow C p)) ∂(dwellM G C)) = ∫ p, f p ∂(prior G n) := by
    have hp := board (G := G) C
    have he := integral_map (f := f) hp.aemeasurable (by rw [hp.map_eq]; exact h'.aestronglyMeasurable)
    rw [hp.map_eq] at he; exact he.symm
  rw [← hm _ HT]
  have hp := partition_pos (G := G) (n := n) β
  exact mul_nonneg (by positivity) (insidePos C β F H hβ ((board C).integrable_comp_of_integrable HT))
end YM.Slice
