import ChallengeSpec

/-! Audit probe (group: translations, joint spectral measure, W0).
Checks how the W0 / EnergyMomentumMeasure statements elaborate. -/

open MeasureTheory YangMills

/-! (1) Instances actually used on `Spacetime`. -/
#synth MeasurableSpace Spacetime
#synth BorelSpace Spacetime
#synth Inner ℝ Spacetime
#synth SecondCountableTopology Spacetime
#synth CompleteSpace Spacetime

example : (inferInstance : MeasurableSpace Spacetime) = borel Spacetime :=
  BorelSpace.measurable_eq

/-! (2) Elaborated statements of the audited fields. -/
set_option pp.explicit true in
#check @WightmanTheory.W0.spectralRepresentation
#check @EnergyMomentumMeasure.selfAdjoint
set_option pp.explicit true in
#check @EnergyMomentumMeasure.countablyAdditive
#check @EnergyMomentumMeasure.diagonalIdentity
#check @WightmanTheory.W0.positiveEnergy
#check @WightmanTheory.W0.uniqueVacuum
#check @TranslationAction.stronglyContinuous

/-! (3) `charFun` is the Euclidean-pairing transform with `+i`. -/
example (μ : Measure Spacetime) (t : Spacetime) :
    charFun μ t = ∫ p, Complex.exp (((∑ i, t i * p i : ℝ) : ℂ) * Complex.I) ∂μ := by
  simp only [charFun_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

example (μ : Measure Spacetime) (t : Spacetime) :
    charFun μ t = ∫ p, Complex.exp (((∑ i, p i * t i : ℝ) : ℂ) * Complex.I) ∂μ := by
  rw [charFun_apply]; congr 1; funext p; simp [PiLp.inner_apply, mul_comm]

/-- Pure time translation by `s` pairs with the last coordinate `time p` with sign `+i`. -/
theorem probe_time_pairing (μ : Measure Spacetime) (s : ℝ) :
    charFun μ (EuclideanSpace.single timeAxis s) =
      ∫ p, Complex.exp (((s * time p : ℝ) : ℂ) * Complex.I) ∂μ := by
  simp only [charFun_apply, EuclideanSpace.inner_single_right, conj_trivial, time]

/-! (4) The complement of the forward cone is a Borel set. -/
theorem probe_spatial_continuous : Continuous spatial := by
  unfold spatial; fun_prop

theorem probe_spatial_continuous' : Continuous spatial :=
  (PiLp.continuous_toLp (p := 2) (β := fun _ : SpaceAxis => ℝ)).comp
    (continuous_pi fun i => PiLp.continuous_apply (p := 2) (β := fun _ : Axis => ℝ) i.castSucc)

theorem probe_time_continuous : Continuous time :=
  PiLp.continuous_apply (p := 2) (β := fun _ : Axis => ℝ) timeAxis

theorem probe_forwardCone_closed : IsClosed forwardCone :=
  isClosed_le (continuous_norm.comp probe_spatial_continuous') probe_time_continuous

theorem probe_cone_compl_measurable : MeasurableSet forwardConeᶜ :=
  probe_forwardCone_closed.measurableSet.compl

/-! (5) The global instance from `attribute [instance] finite`, and uniqueness:
the spectral representation pins down `diagonal`, hence `projection` on Borel sets. -/
section
variable {H : HilbertSpace}

example (E : EnergyMomentumMeasure H) (ψ : H.carrier) : IsFiniteMeasure (E.diagonal ψ) :=
  inferInstance

theorem probe_diagonal_unique (U : TranslationAction H) (E₁ E₂ : EnergyMomentumMeasure H)
    (h₁ : ∀ ψ x, charFun (E₁.diagonal ψ) x = inner ℂ ψ (U.operator x ψ))
    (h₂ : ∀ ψ x, charFun (E₂.diagonal ψ) x = inner ℂ ψ (U.operator x ψ)) (ψ : H.carrier) :
    E₁.diagonal ψ = E₂.diagonal ψ :=
  Measure.ext_of_charFun (funext fun x => (h₁ ψ x).trans (h₂ ψ x).symm)

theorem probe_projection_unique (U : TranslationAction H) (E₁ E₂ : EnergyMomentumMeasure H)
    (h₁ : ∀ ψ x, charFun (E₁.diagonal ψ) x = inner ℂ ψ (U.operator x ψ))
    (h₂ : ∀ ψ x, charFun (E₂.diagonal ψ) x = inner ℂ ψ (U.operator x ψ))
    {B : Set Spacetime} (hB : MeasurableSet B) : E₁.projection B = E₂.projection B := by
  have key : ∀ ψ : H.carrier,
      inner ℂ ψ (E₁.projection B ψ) = inner ℂ ψ (E₂.projection B ψ) := by
    intro ψ
    rw [← E₁.diagonalIdentity hB ψ, ← E₂.diagonalIdentity hB ψ,
      probe_diagonal_unique U E₁ E₂ h₁ h₂ ψ]
  apply ContinuousLinearMap.coe_injective
  refine (ext_inner_map _ _).1 fun ψ => ?_
  have := congrArg (starRingEnd ℂ) (key ψ)
  simpa using this

/-- `positiveEnergy` really forces every diagonal measure to vanish off the closed cone. -/
theorem probe_support {Labels : FieldLabels} (T : WightmanTheory H Labels) (h : T.W0)
    (ψ : H.carrier) : T.energyMomentum.diagonal ψ forwardConeᶜ = 0 := by
  have h0 : (T.energyMomentum.diagonal ψ).real forwardConeᶜ = 0 := by
    have := T.energyMomentum.diagonalIdentity probe_cone_compl_measurable ψ
    rw [h.positiveEnergy] at this
    simpa using this
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at h0
  exact h0.resolve_right (measure_ne_top _ _)

end

#print axioms probe_time_pairing
#print axioms probe_cone_compl_measurable
#print axioms probe_projection_unique
#print axioms probe_support
