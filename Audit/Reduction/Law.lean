import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Square complex matrices form a second-countable space (`Matrix` is a type synonym for
`Fin k → Fin k → ℂ`, but instance search does not see through it). -/
theorem matrix_secondCountable (k : ℕ) : SecondCountableTopology (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin k → ℂ))

/-- The unitary group carries the subspace topology of the matrices, so it is second countable. -/
theorem unitary_secondCountable (k : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin k) ℂ) := by
  haveI := matrix_secondCountable k
  exact TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val

/-- The gauge group carries the subspace topology of the unitary group. -/
theorem image_secondCountable (g : GaugeGroup) : SecondCountableTopology g.image := by
  haveI := unitary_secondCountable (g.n + 1)
  exact TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val

/-- The Wilson energy is a continuous function of the configuration. -/
theorem wilsonEnergy_continuous (g : GaugeGroup) (l : ℕ+) :
    Continuous (fun U : Configuration g l => wilsonEnergy U) := by
  unfold wilsonEnergy
  refine continuous_finsetSum _ (fun p _ => ?_)
  refine continuous_const.sub ((Complex.continuous_re.comp ?_).div_const _)
  refine Continuous.matrix_trace ?_
  refine continuous_subtype_val.comp (continuous_subtype_val.comp ?_)
  unfold plaquette
  fun_prop

/-- The real part of the trace of a gauge-group element is bounded by the matrix size. -/
theorem abs_re_trace_le (g : GaugeGroup) (P : g.image) :
    |(P.val.val.trace).re| ≤ ((g.n + 1 : ℕ) : ℝ) := by
  have hmem : P.val.val ∈ Matrix.unitaryGroup (Fin (g.n + 1)) ℂ := P.val.prop
  calc |(P.val.val.trace).re| ≤ ‖P.val.val.trace‖ := Complex.abs_re_le_norm _
    _ = ‖∑ i, P.val.val i i‖ := rfl
    _ ≤ ∑ i, ‖P.val.val i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (g.n + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary hmem i i
    _ = ((g.n + 1 : ℕ) : ℝ) := by simp

/-- Each plaquette term of the Wilson energy lies in `[-2, 2]`. -/
theorem abs_plaquetteTerm_le (g : GaugeGroup) (P : g.image) :
    |1 - (P.val.val.trace).re / ((g.n + 1 : ℕ) : ℝ)| ≤ 2 := by
  have h1 := abs_re_trace_le g P
  have hpos : (0 : ℝ) < ((g.n + 1 : ℕ) : ℝ) := by positivity
  rw [abs_le] at h1 ⊢
  have hle : (P.val.val.trace).re / ((g.n + 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hpos).mpr h1.2
  have hge : -1 ≤ (P.val.val.trace).re / ((g.n + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ hpos]; linarith
  constructor <;> linarith

/-- The Wilson energy is uniformly bounded. -/
theorem abs_wilsonEnergy_le (g : GaugeGroup) (l : ℕ+) (U : Configuration g l) :
    |wilsonEnergy U| ≤ ∑ _p : Site l × Directions, (2 : ℝ) := by
  unfold wilsonEnergy
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun p _ => abs_plaquetteTerm_le g _)

/-- The unnormalized Wilson weight is uniformly bounded. -/
theorem wilsonWeight_le (g : GaugeGroup) (l : ℕ+) (β : ℝ) (U : Configuration g l) :
    ‖Real.exp (-β * wilsonEnergy U)‖ ≤ Real.exp (|β| * ∑ _p : Site l × Directions, (2 : ℝ)) := by
  have hle : -β * wilsonEnergy U ≤ |β| * ∑ _p : Site l × Directions, (2 : ℝ) :=
    calc -β * wilsonEnergy U ≤ |-β * wilsonEnergy U| := le_abs_self _
      _ = |β| * |wilsonEnergy U| := by rw [abs_mul, abs_neg]
      _ ≤ |β| * ∑ _p : Site l × Directions, (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (abs_wilsonEnergy_le g l U) (abs_nonneg β)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr hle

/-- The unnormalized Wilson weight is integrable against the product Haar prior. -/
theorem wilsonWeight_integrable (g : GaugeGroup) (l : ℕ+) (β : ℝ) (μ : Measure g.image)
    [IsProbabilityMeasure μ] :
    Integrable (fun U : Configuration g l => Real.exp (-β * wilsonEnergy U))
      (Measure.pi fun _ => μ) := by
  haveI := image_secondCountable g
  have hcont : Continuous (fun U : Configuration g l => Real.exp (-β * wilsonEnergy U)) :=
    Real.continuous_exp.comp (continuous_const.mul (wilsonEnergy_continuous g l))
  exact Integrable.of_bound hcont.aestronglyMeasurable _
    (ae_of_all _ fun U => wilsonWeight_le g l β U)

/-- The normalized Wilson law is a probability measure. -/
theorem wilsonLaw_isProbability (g : GaugeGroup) (l : ℕ+) (β : ℝ) (μ : Measure g.image)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (wilsonLaw g l β μ) := by
  have h := isProbabilityMeasure_tilted (μ := Measure.pi fun _ : Site l × Axis => μ)
    (f := fun U => -β * wilsonEnergy U) (wilsonWeight_integrable g l β μ)
  exact h

/-- Finite moments of the gauge-blind family are the indicator `allZero`. -/
theorem blind_finiteMoment {g : GaugeGroup} (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (F : ℕ → Type) [∀ d, Zero (F d)] (N p : ℕ) {n : ℕ}
    (v : Fin n → Σ d, F d)
    (x : Fin n → Site ((blindFamily μ hH F).period p * (blindFamily μ hH F).denominator N)) :
    (blindFamily μ hH F).finiteMoment N p v x = allZero v := by
  haveI := (blindFamily μ hH F).probability
  haveI := wilsonLaw_isProbability g ((blindFamily μ hH F).period p *
    (blindFamily μ hH F).denominator N) ((blindFamily μ hH F).beta N p) (blindFamily μ hH F).haar
  have hconst : ∀ U, (∏ i, (blindFamily μ hH F).insertion N p (v i) (x i) U) = allZero v := by
    intro U
    classical
    show (∏ i, (if v i = zeroTag F then (1 : ℂ) else 0)) = allZero v
    unfold allZero
    by_cases h : ∀ i, v i = zeroTag F
    · rw [if_pos h]
      exact Finset.prod_eq_one (fun i _ => if_pos (h i))
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  unfold WilsonFamily.finiteMoment
  simp only [hconst, integral_const, probReal_univ, one_smul]

end YMAudit
