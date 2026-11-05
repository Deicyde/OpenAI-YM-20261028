import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Meristem


/-!
# Supplying strong measurability for integrals after Coordinate changes

 All jets dominated *on a neighborhood*. Strong meas even without
 continuity of held labels/tag probability. Use `Meristem` under μ.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Meristem
open Filter Function MeasureTheory
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {E F α : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]  [MeasurableSpace α]
open Brush
variable {x:E} {k j : ℕ} {f : α→ E→F} {S : Set E} (h : IsOpen S)

include h
lemma slopes (he:x∈S) (hh : ∀ y∈S,StronglyMeasurable fun i=> f i y) (hp : ∀ i,DifferentiableAt ℝ (f i) x) :
    StronglyMeasurable fun i=> fderiv ℝ (f i) x := by
  let L i:= fderiv ℝ (f i) x
  have hf v : StronglyMeasurable fun i=> L i v := by
    let A (p:ℝ) i:= p⁻¹ • (f i (x+p • v)-f i x)
    let q:= 𝓝[≠] (0:ℝ)
    have hx i : Tendsto (fun p=> A p i) q (𝓝 (L i v)) := (hp i).hasFDerivAt.hasLineDerivAt v |>.tendsto_slope_zero
    let g p := if x+p • v∈ S then A p else 0
    have hg : ∀ p, StronglyMeasurable (g p) := by
      intro p; unfold g; split
      next ht=> exact StronglyMeasurable.smul (stronglyMeasurable_const (b:=p⁻¹)) ((hh _ ht).sub (hh x he))
      exact stronglyMeasurable_const
    have ht : g=ᶠ[q] A := by
      have hp : ∀ᶠ v in 𝓝 (0:ℝ), x+ v • (show E from _) ∈ S :=
        (show Continuous fun z:ℝ=> x+z • v by fun_prop).continuousAt.eventually (h.mem_nhds (by simpa))
      filter_upwards [hp.filter_mono nhdsWithin_le_nhds] with i hi using if_pos hi
    refine stronglyMeasurable_of_tendsto (𝓝[≠] (0:ℝ)) hg ((tendsto_pi_nhds.mpr hx).congr' ht.symm)
  let b:= Module.finBasis ℝ E
  let g i p:= (b.coord i).toContinuousLinearMap.smulRight (p:F)
  have he (i):Continuous (g i) := by unfold g; fun_prop
  have hp i : L i=∑ j, g j (L i (b j)) := by
    ext1 x'; conv_lhs => arg 2; rw [← b.sum_repr x']
    rw [map_sum]
    simp [g]
  have heq : L = fun i=>∑ j,g j (L i (b j)) := funext hp
  change StronglyMeasurable L; nth_rw 1 [heq]
  exact Finset.stronglyMeasurable_fun_sum _ (fun i _=> (he i).comp_stronglyMeasurable (hf (b i)))

-- recurse jets
lemma legs (hp : ∀ i,∀ y∈S, ContDiffAt ℝ (↑j : WithTop ℕ∞) (f i) y) (hh : ∀ y∈S, StronglyMeasurable fun i=> f i y)
    (hk:k ≤ j) (he:x∈S) : StronglyMeasurable fun i=> iteratedFDeriv ℝ k (f i) x := by
  induction k generalizing x with
  | zero => exact (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp_stronglyMeasurable (hh x he)
  | succ k ih =>
    simp_rw [iteratedFDeriv_succ_eq_comp_left]; refine (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1)=> E) F).symm.continuous.comp_stronglyMeasurable ?_
    exact slopes h he (fun y hy=> ih (by omega) hy) (fun i=> (hp i x he).differentiableAt_iteratedFDeriv
      (by exact_mod_cast (hk : k < j)))

variable (U : E → α → ℝ) (μ : Measure α)
omit h
lemma points (p : ∃ B : α→ℝ, Integrable B μ ∧ ∀ᶠ y in 𝓝 x, ∀ i, Brush j (B i) 1 (fun y=> U y i) y)
    (hM : ∀ᶠ y in 𝓝 x, Measurable (U y)) : Meristem U x μ j ∧ ∀ᶠ y in 𝓝 x, Integrable (U y) μ := by
  obtain ⟨B,hF,hP⟩:=p
  constructor
  · obtain ⟨O,hS,hO,hx⟩:= _root_.mem_nhds_iff.mp (hP.and hM)
    have ht (i:E) (hi:i∈O) : (∀ v, Brush j (B v) 1 (fun t=>U t v) i) ∧ Measurable (U i) := hS hi
    refine ⟨O,hO.mem_nhds hx,ae_of_all _ (fun _ t h=>(ht t h).1 _ |>.1),fun k hk=> ⟨B,hF,fun y hy=> ?_,ae_of_all _ fun i y hy=>?_⟩⟩
    · exact (legs (f:=Function.swap U) hO (fun i t h=> ((ht t h).1 i).smooth) (fun i hi=> ((ht i hi).2.stronglyMeasurable)) hk hy).aestronglyMeasurable
    exact (Brush.offer.1 ((ht _ hy).1 i)).inside k hk
  filter_upwards [hP,hM] with t hp ht; exact hF.mono' ht.aestronglyMeasurable (ae_of_all _ fun i=> (hp i).bound)
end YM.ConnectedActivityE6.Blaze.Meristem
