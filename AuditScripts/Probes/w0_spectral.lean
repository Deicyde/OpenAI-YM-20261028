import ChallengeSpec

/-! Audit probe for translations, the joint spectral measure and W0
(PublicTheory.lean lines 165-206 and 268-278). Checks
(0) elaborated instances in `W0.spectralRepresentation`,
(1) measurability of `forwardConeᶜ` (so `positiveEnergy` is not a junk value),
(2) the Euclidean pairing inside `charFun`,
(3) that the sign convention binds: negative energy is rejected,
(4) a Dirac projection-valued measure with arbitrary junk on non-measurable sets,
    which satisfies every `EnergyMomentumMeasure` field, and the positive-energy case,
(5) redundancy of `TranslationAction.identity` and surjectivity of each operator. -/
set_option autoImplicit false
noncomputable section

open YangMills MeasureTheory Complex
open scoped InnerProductSpace ENNReal NNReal

namespace YangMills.AuditW0

/-! (0) Elaborated instances. -/
#synth MeasurableSpace Spacetime
#synth BorelSpace Spacetime
#synth Inner ℝ Spacetime
#synth MeasurableSingletonClass Spacetime
set_option pp.explicit true in
#check @WightmanTheory.W0.spectralRepresentation

/-! (1) `forwardConeᶜ` is open, hence Borel measurable. -/
theorem forwardCone_isClosed : IsClosed forwardCone := by
  unfold forwardCone spatial time
  exact isClosed_le (by fun_prop) (by fun_prop)

theorem forwardCone_compl_measurable : MeasurableSet forwardConeᶜ :=
  forwardCone_isClosed.isOpen_compl.measurableSet

/-! (2) The pairing used by `charFun` is Euclidean, with time last. -/
def eT : Spacetime := EuclideanSpace.single timeAxis 1

theorem inner_eT (a : Spacetime) : ⟪eT, a⟫_ℝ = time a := by
  rw [eT, EuclideanSpace.inner_single_left]
  simp [time]

theorem time_eT : time eT = 1 := by simp [time, eT]

theorem spatial_eT : spatial eT = 0 := by
  ext i
  simp [spatial, eT, Fin.castSucc_ne_last]

theorem eT_mem : eT ∈ forwardCone := by
  show ‖spatial eT‖ ≤ time eT
  rw [spatial_eT, time_eT, norm_zero]
  exact zero_le_one

theorem neg_eT_not_mem : -eT ∉ forwardCone := by
  intro h
  have h' : ‖spatial (-eT)‖ ≤ time (-eT) := h
  have ht : time (-eT) = -1 := by simp [time, eT]
  rw [ht] at h'
  linarith [norm_nonneg (spatial (-eT))]

/-! (3) Translations acting on a unit vector by `exp(-i·time a)` (negative energy in
this convention) admit no measure satisfying `spectralRepresentation` and
`positiveEnergy`. -/
theorem negative_energy_rejected (H : HilbertSpace) (P : EnergyMomentumMeasure H)
    (ψ : H.carrier) (hψ : ‖ψ‖ = 1)
    (hspec : ∀ a : Spacetime, charFun (P.diagonal ψ) a =
      inner ℂ ψ (cexp (-(time a : ℂ) * I) • ψ))
    (hpos : P.projection forwardConeᶜ = 0) : False := by
  have hdiag : P.diagonal ψ = Measure.dirac (-eT) := by
    apply Measure.ext_of_charFun
    funext a
    rw [hspec a, charFun_dirac, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
    simp [inner_neg_left, inner_eT]
  have h := P.diagonalIdentity forwardCone_compl_measurable ψ
  rw [hpos, hdiag] at h
  simp only [ContinuousLinearMap.zero_apply, inner_zero_right] at h
  have h1 : (Measure.dirac (-eT)).real forwardConeᶜ = 1 := by
    rw [measureReal_def, Measure.dirac_apply_of_mem (Set.mem_compl neg_eT_not_mem)]
    simp
  rw [h1] at h
  simp at h

/-! (4) Dirac projection-valued measure at `k`, with an arbitrary operator `junk` on
every non-measurable set. -/
open Classical in
def diracPVM (H : HilbertSpace) (k : Spacetime) (junk : H.Operator) :
    EnergyMomentumMeasure H where
  projection E :=
    if MeasurableSet E then (if k ∈ E then ContinuousLinearMap.id ℂ H.carrier else 0)
    else junk
  empty := by simp
  univ := by simp
  intersection := by
    intro L R hL hR
    simp only [hL, hR, hL.inter hR, ↓reduceIte]
    by_cases h1 : k ∈ L <;> by_cases h2 : k ∈ R <;> simp [h1, h2]
  selfAdjoint := by
    intro E hE
    simp only [hE, ↓reduceIte]
    split_ifs <;> simp
  countablyAdditive := by
    intro E hE hdisj ψ
    have hU : MeasurableSet (⋃ i, E i) := MeasurableSet.iUnion hE
    simp only [hE, hU, ↓reduceIte]
    by_cases h : ∃ i, k ∈ E i
    · obtain ⟨i, hi⟩ := h
      have hmem : k ∈ ⋃ i, E i := Set.mem_iUnion.2 ⟨i, hi⟩
      have hf : ∀ j, j ≠ i →
          (if k ∈ E j then ContinuousLinearMap.id ℂ H.carrier else 0) ψ = 0 := by
        intro j hj
        have hkj : k ∉ E j := fun hk => Set.disjoint_left.1 (hdisj hj) hk hi
        simp [hkj]
      have hs := hasSum_single (f := fun j =>
        (if k ∈ E j then ContinuousLinearMap.id ℂ H.carrier else 0) ψ) i hf
      simp only [hi, hmem, ↓reduceIte] at hs ⊢
      exact hs
    · push_neg at h
      have hnot : k ∉ ⋃ i, E i := by simpa using h
      simp only [h, hnot, ↓reduceIte, ContinuousLinearMap.zero_apply]
      exact hasSum_zero
  diagonal ψ := (‖ψ‖₊ ^ 2) • Measure.dirac k
  finite ψ := by first | infer_instance | (dsimp only; infer_instance)
  diagonalIdentity := by
    intro E hE ψ
    simp only [hE, ↓reduceIte]
    rw [measureReal_nnreal_smul_apply, measureReal_def, Measure.dirac_apply' k hE]
    by_cases hk : k ∈ E
    · rw [Set.indicator_of_mem hk]
      simp only [Pi.one_apply, ENNReal.toReal_one, mul_one, if_pos hk,
        ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    · rw [Set.indicator_of_notMem hk]
      simp [hk]

open Classical in
theorem diracPVM_projection (H : HilbertSpace) (k : Spacetime) (junk : H.Operator)
    (E : Set Spacetime) :
    (diracPVM H k junk).projection E =
      if MeasurableSet E then (if k ∈ E then ContinuousLinearMap.id ℂ H.carrier else 0)
      else junk := rfl

/-- Junk on non-measurable sets is unconstrained. -/
example (H : HilbertSpace) (k : Spacetime) (junk : H.Operator) (N : Set Spacetime)
    (hN : ¬ MeasurableSet N) : (diracPVM H k junk).projection N = junk := by
  rw [diracPVM_projection, if_neg hN]

/-- Spectral representation of the one-dimensional character `exp(i⟪k,a⟫)`. -/
theorem dirac_spectral (H : HilbertSpace) (k : Spacetime) (junk : H.Operator)
    (ψ : H.carrier) (a : Spacetime) :
    charFun ((diracPVM H k junk).diagonal ψ) a =
      inner ℂ ψ (cexp (⟪k, a⟫_ℝ * I) • ψ) := by
  show charFun ((‖ψ‖₊ ^ 2) • Measure.dirac k) a = _
  rw [charFun_apply, integral_smul_nnreal_measure, integral_dirac, inner_smul_right,
    inner_self_eq_norm_sq_to_K, NNReal.smul_def, Complex.real_smul]
  push_cast
  exact mul_comm _ _

/-- Positive energy holds exactly when `k` lies in the closed forward cone. -/
theorem dirac_positiveEnergy (H : HilbertSpace) (k : Spacetime) (hk : k ∈ forwardCone)
    (junk : H.Operator) : (diracPVM H k junk).projection forwardConeᶜ = 0 := by
  rw [diracPVM_projection, if_pos forwardCone_compl_measurable, if_neg (fun h => h hk)]

/-- The positive-energy character `exp(+i·time a)` is accepted. -/
example (H : HilbertSpace) (junk : H.Operator) (ψ : H.carrier) (a : Spacetime) :
    charFun ((diracPVM H eT junk).diagonal ψ) a =
      inner ℂ ψ (cexp ((time a : ℂ) * I) • ψ) := by
  rw [dirac_spectral, inner_eT]

example (H : HilbertSpace) (junk : H.Operator) :
    (diracPVM H eT junk).projection forwardConeᶜ = 0 :=
  dirac_positiveEnergy H eT eT_mem junk

/-- The trivial representation with the Dirac measure at `0` satisfies the spectral
representation and positive energy (the one-dimensional vacuum sector). -/
example (H : HilbertSpace) (junk : H.Operator) (ψ : H.carrier) (a : Spacetime) :
    charFun ((diracPVM H 0 junk).diagonal ψ) a = inner ℂ ψ ψ := by
  rw [dirac_spectral]
  simp

example (H : HilbertSpace) (junk : H.Operator) :
    (diracPVM H 0 junk).projection forwardConeᶜ = 0 :=
  dirac_positiveEnergy H 0 (by simp [forwardCone, time, spatial]; rfl) junk

/-- Cross-check with W2: the translation-invariant vectors are exactly `ℂ • Ω`. -/
example {H : HilbertSpace} {Labels : FieldLabels} (theory : WightmanTheory H Labels)
    (h0 : theory.W0) (h2 : theory.W2) (ψ : H.carrier) :
    (∀ x, theory.translations.operator x ψ = ψ) ↔
      ∃ c : ℂ, c • theory.fields.vacuum.1 = ψ := by
  constructor
  · exact h0.uniqueVacuum ψ
  · rintro ⟨c, rfl⟩ x
    rw [map_smul, ← theory.translationCompatibility x,
      h2.vacuumInvariant (theory.poincare.pureTranslation x)]

/-- Cross-check with the Poincaré action: pure translations pull tests back by `y - x`,
so W2 reads `U(x) φ(f) U(x)⁻¹ = φ(f(· - x))`. -/
example {H : HilbertSpace} {Labels : FieldLabels} (A : PoincareAction H Labels)
    (x : Spacetime) (f : TestFunction) (y : Spacetime) :
    A.onTests (A.pureTranslation x) f y = f (y - x) := by
  rw [A.pullback, (A.translationCoordinates x).1, (A.translationCoordinates x).2]
  simp

/-- `selfAdjoint` already follows from `diagonalIdentity` (real quadratic form). -/
theorem selfAdjoint_redundant (H : HilbertSpace) (P : EnergyMomentumMeasure H)
    {E : Set Spacetime} (hE : MeasurableSet E) : IsSelfAdjoint (P.projection E) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have h := P.diagonalIdentity hE v
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm (P.projection E v) v, ← h]
  simp [Complex.conj_ofReal]

/-! (5) Translation-action redundancies. -/
theorem identity_redundant (H : HilbertSpace) (op : Spacetime → H.Operator)
    (add : ∀ x y, (op x).comp (op y) = op (x + y))
    (iso : ∀ x (ψ : H.carrier), ‖op x ψ‖ = ‖ψ‖) :
    op 0 = ContinuousLinearMap.id ℂ _ := by
  ext ψ
  have h : op 0 (op 0 ψ) = op 0 ψ := by
    have := congrArg (fun T : H.Operator => T ψ) (add 0 0)
    simpa using this
  have h2 : ‖op 0 ψ - ψ‖ = 0 := by
    rw [← iso 0 (op 0 ψ - ψ), map_sub, h, sub_self, norm_zero]
  simpa [sub_eq_zero] using h2

theorem operator_surjective (H : HilbertSpace) (T : TranslationAction H) (x : Spacetime) :
    Function.Surjective (T.operator x) := fun ψ =>
  ⟨T.operator (-x) ψ, by
    have := congrArg (fun A : H.Operator => A ψ) (T.add x (-x))
    simpa [T.identity] using this⟩

end YangMills.AuditW0
