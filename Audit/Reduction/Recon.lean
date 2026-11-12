import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

section ReconHelpers

open scoped ContDiff

/-- `allZero` is invariant under reindexing by an equivalence. -/
private theorem allZero_comp_equiv {F : ℕ → Type} [∀ d, Zero (F d)] {ι κ : Type}
    (w : ι → Σ d, F d) (e : κ ≃ ι) : allZero (w ∘ e) = allZero w := by
  unfold allZero
  by_cases h : ∀ i, w i = zeroTag F
  · rw [if_pos h]
    exact if_pos (fun k => h (e k))
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    intro i
    simpa using h' (e.symm i)

/-- The two phases are distinct. -/
private theorem phase1_ne_phase0 : phase1 ≠ phase0 := by
  intro h
  have h' := congrArg Subtype.val h
  simp [phase0, phase1] at h'

/-- Every phase is `phase0` or `phase1`. -/
private theorem phase_cases (p : Phase) : p = phase0 ∨ p = phase1 := by
  obtain ⟨v, hv⟩ := p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · left; rfl
  · right; rfl

/-- The uniform measure on the two phases is a probability measure. -/
private theorem phaseMeasure_isProbability : IsProbabilityMeasure phaseMeasure := by
  constructor
  simp only [phaseMeasure, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- The uniform measure on the two phases charges every nonempty open set. -/
private theorem phaseMeasure_isOpenPos : phaseMeasure.IsOpenPosMeasure := by
  refine ⟨fun U _ hne => ?_⟩
  obtain ⟨p, hp⟩ := hne
  simp only [phaseMeasure, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  refine mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) ?_
  rcases phase_cases p with rfl | rfl
  · rw [Measure.dirac_apply_of_mem hp]
    simp
  · rw [Measure.dirac_apply_of_mem hp]
    simp

variable {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)

private theorem redCorrelation_none {n : ℕ} (w : Fin n → T₀.Tag) (x : Points n) :
    redCorrelation T₀ none w x = allZero w := rfl

private theorem redCorrelation_phase0 {n : ℕ} (w : Fin n → T₀.Tag) (x : Points n) :
    redCorrelation T₀ (some phase0) w x = T₀.correlation (some T₀.selected) w x := by
  simp only [redCorrelation, ↓reduceIte]

private theorem redCorrelation_of_ne {n : ℕ} {i : Phase} (hi : i ≠ phase0) (w : Fin n → T₀.Tag)
    (x : Points n) :
    redCorrelation T₀ (some i) w x = 2 * allZero w - T₀.correlation (some T₀.selected) w x := by
  simp only [redCorrelation]
  exact if_neg hi

private theorem redCorrelation_perm (hR : T₀.Reconstructed) (s : Option Phase) {n : ℕ}
    (a : Fin n → T₀.Tag) (x : Points n) (hx : x ∈ WilsonFamily.separated n)
    (π : Equiv.Perm (Fin n)) :
    redCorrelation T₀ s (a ∘ π) (WithLp.toLp 2 (x.ofLp ∘ π)) = redCorrelation T₀ s a x := by
  have hA : allZero (a ∘ π) = allZero a := allZero_comp_equiv a π
  have hS := hR.permutation (some T₀.selected) a x hx π
  cases s with
  | none => exact hA
  | some i =>
    by_cases hi : i = phase0
    · subst hi
      rw [redCorrelation_phase0, redCorrelation_phase0, hS]
    · rw [redCorrelation_of_ne T₀ hi, redCorrelation_of_ne T₀ hi, hS, hA]

private theorem redCorrelation_smooth (hR : T₀.Reconstructed) (s : Option Phase) {n : ℕ}
    (a : Fin n → T₀.Tag) :
    ContDiffOn ℝ ∞ (redCorrelation T₀ s a) (WilsonFamily.separated n) := by
  cases s with
  | none =>
    have h : redCorrelation T₀ none a = fun _ => allZero a := by
      funext x
      exact redCorrelation_none T₀ a x
    rw [h]
    exact contDiffOn_const
  | some i =>
    by_cases hi : i = phase0
    · have h : redCorrelation T₀ (some i) a = T₀.correlation (some T₀.selected) a := by
        funext x
        subst hi
        exact redCorrelation_phase0 T₀ a x
      rw [h]
      exact hR.smooth (some T₀.selected) a
    · have h : redCorrelation T₀ (some i) a =
          fun x => 2 * allZero a - T₀.correlation (some T₀.selected) a x := by
        funext x
        exact redCorrelation_of_ne T₀ hi a x
      rw [h]
      exact contDiffOn_const.sub (hR.smooth (some T₀.selected) a)

private theorem redCorrelation_continuous {n : ℕ} (a : Fin n → T₀.Tag) (x : Points n) :
    Continuous (fun i : Phase => redCorrelation T₀ (some i) a x) :=
  continuous_of_discreteTopology

private theorem redCorrelation_mixture {n : ℕ} (a : Fin n → T₀.Tag) (x : Points n) :
    (∫ i, redCorrelation T₀ (some i) a x ∂phaseMeasure) = redCorrelation T₀ none a x := by
  have hi0 : Integrable (fun i : Phase => redCorrelation T₀ (some i) a x)
      (Measure.dirac phase0) := Integrable.of_finite
  have hi1 : Integrable (fun i : Phase => redCorrelation T₀ (some i) a x)
      (Measure.dirac phase1) := Integrable.of_finite
  rw [phaseMeasure, integral_smul_measure, integral_add_measure hi0 hi1, integral_dirac,
    integral_dirac, redCorrelation_phase0, redCorrelation_of_ne T₀ phase1_ne_phase0,
    redCorrelation_none, ENNReal.toReal_inv, ENNReal.toReal_ofNat, Complex.real_smul]
  push_cast
  ring

end ReconHelpers

/-- The reduced hierarchy satisfies `Reconstructed`: the selected-phase clauses are `T₀`'s,
and the two phases average to the Wilson limit `allZero`. -/
theorem reduced_reconstructed {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure)
    (hR : T₀.Reconstructed) : (reduced T₀ μ hH).Reconstructed := by
  exact
    { axioms := hR.axioms
      faithful := hR.faithful
      injective := hR.injective
      acts := hR.acts
      covers := hR.covers
      represents := Function.surjective_id
      normalized := phaseMeasure_isProbability
      fullSupport := phaseMeasure_isOpenPos
      permutation := fun s _ a x hx π => redCorrelation_perm T₀ hR s a x hx π
      smooth := fun s _ a => redCorrelation_smooth T₀ hR s a
      characterContinuity := fun a x _ => redCorrelation_continuous T₀ a x
      mixture := fun a x _ => redCorrelation_mixture T₀ a x
      analytic := hR.analytic
      root := fun v x h => (hR.root v x h).trans (redCorrelation_phase0 T₀ v x).symm
      boundary := hR.boundary }

end YMAudit
