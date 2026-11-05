import YM.Gauge.MatrixGroup
import YM.Lattice.Faces
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The physical Wilson law

The *actual* normalized and unnormalized densities on one torus.
One copy per oriented positive-axis face (`i<j`); no half-volume correction.
Normalized expectation is a Bochner integral; callers must still prove
integrability (e.g. the continuous and bounded cylinders). Do not treat the
`integral_undef` value as an expectation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Wilson

open MeasureTheory Set Filter Lattice
open scoped Matrix.Norms.Frobenius ENNReal NNReal Topology

abbrev Config (G : Gauge) (n : Side) := Links (Per n) G.El
abbrev CoverConfig (G : Gauge) := Links ℤ G.El

variable {G : Gauge} {n : Side}

def energy (U : Config G n) : ℝ := ∑ p : Face (Per n), G.price (faceValue U p)

theorem energy_nonneg (U : Config G n) : 0 ≤ energy U :=
  Finset.sum_nonneg fun _ _ ↦ (G.price_range _).1

@[fun_prop] theorem continuous_travel {R : Type*} [AddCommGroup R] [One R]
    (w : Walk) (x : Four R) : Continuous fun U : Links R G.El => travel U x w := by
  induction w generalizing x with
  | nil => exact continuous_const
  | cons d l ih =>
    simp only [travel]; apply Continuous.mul _ (ih _)
    simp only [Step.read]; split <;> fun_prop

@[fun_prop] theorem energy_cont : Continuous (energy : Config G n → ℝ) := by
  unfold energy faceValue; fun_prop

theorem energy_pull (U : Config G n) (s : Signed) (t : Site n) :
    energy (pull s t U) = energy U := by
  simp only [energy, Face.send_price U _ s t G.price (G.price_inv) (fun k g ↦ G.price_conj g k)]
  let e : Equiv.Perm (Face (Per n)) := Equiv.ofBijective (Face.send s t)
    ⟨Face.injective_send s t, (Finite.injective_iff_surjective).mp (Face.injective_send s t)⟩
  exact Equiv.sum_comp e fun p => G.price (faceValue U p)

theorem energy_gauge (U : Config G n) (t : Site n → G.El) : energy (gauge t U) = energy U := by
  simp [energy]

def prior (G : Gauge) (n : Side) : Measure (Config G n) := Measure.pi (fun _ => G.probHaar)
instance : IsProbabilityMeasure (prior G n) := by unfold prior; infer_instance

def bare (β : ℝ) (U : Config G n) : ℝ := Real.exp (-β * energy U)
theorem bare_pos (β : ℝ) (U : Config G n) : 0 < bare β U := Real.exp_pos _

@[fun_prop] theorem bare_cont (β : ℝ) : Continuous (bare β : Config G n → ℝ) := by unfold bare; fun_prop
@[fun_prop] theorem measurable_bare (β : ℝ) : Measurable (bare β : Config G n → ℝ) :=
  (bare_cont _).measurable

@[simp] theorem bare_pull (β : ℝ) (U : Config G n) (s : Signed) t :
    bare β (pull s t U) = bare β U := by unfold bare; rw [energy_pull]

@[simp] theorem bare_gauge (β : ℝ) (U : Config G n) t :
    bare β (gauge t U) = bare β U := by unfold bare; rw [energy_gauge]

theorem bare_integrable (β : ℝ) : Integrable (bare β) (prior G n) :=
  (bare_cont _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def partition (G : Gauge) (n : Side) (β : ℝ) := ∫ U, bare β U ∂(prior G n)

theorem partition_pos (β : ℝ) : 0 < partition G n β := by
  apply (integral_pos_iff_support_of_nonneg (fun U => (bare_pos β U).le) (bare_integrable β)).mpr
  have hs : Function.support (bare β : Config G n → ℝ) = univ :=
    Set.eq_univ_of_forall (fun x ↦ (bare_pos _ x).ne')
  simp [hs]

def weight (β : ℝ) (U : Config G n) : ℝ≥0∞ := ENNReal.ofReal (bare β U / partition G n β)

@[fun_prop] theorem weight_meas (β : ℝ) : Measurable (weight β : Config G n → ℝ≥0∞) :=
  ((measurable_bare _).div_const _).ennreal_ofReal

def law (G : Gauge) (n : Side) (β : ℝ) : Measure (Config G n) := (prior G n).withDensity (weight β)

instance (β : ℝ) : IsProbabilityMeasure (law G n β) where
  measure_univ := by
    have hfin : Integrable (fun U : Config G n => bare β U / partition G n β) (prior G n) :=
      (bare_integrable β).div_const _
    rw [law, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    unfold weight; rw [← ofReal_integral_eq_lintegral_ofReal hfin]
    · rw [integral_div, ← partition, div_self (partition_pos β).ne', ENNReal.ofReal_one]
    exact Eventually.of_forall fun U ↦ (div_pos (bare_pos _ _) (partition_pos _)).le

/-- Use with integrable functions only. -/
def moment (β : ℝ) (F : Config G n → ℂ) := ∫ U, F U ∂(law G n β)

theorem continuous_integrable {X : Type*} [NormedAddCommGroup X]
    (β : ℝ) {F : Config G n → X} (hf : Continuous F) : Integrable F (law G n β) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem bounded_integrable (β : ℝ) {F : Config G n → ℂ} (hm : Measurable F)
    {C : ℝ} (hf : ∀ x, ‖F x‖ ≤ C) : Integrable F (law G n β) :=
  Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hf)

/-- Rewrite law back in terms of unnormalized weight. -/
theorem moment_formula (β : ℝ) (F : Config G n → ℂ) (_ : Integrable F (law G n β)) :
    moment β F = (partition G n β : ℂ)⁻¹ * ∫ U, (bare β U : ℂ) * F U ∂(prior G n) := by
  unfold moment law
  rw [integral_withDensity_eq_integral_toReal_smul (weight_meas β)]
  · simp only [weight]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (div_pos (bare_pos _ x) (partition_pos _)).le,
      Complex.real_smul, Complex.ofReal_div, div_eq_mul_inv]
    ring
  exact Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
end YM.Wilson
