import ChallengeSpec

/-! Audit probe: Euclidean-to-Wightman reconstruction bridge (`ChallengeSpec.lean` 94-143).

Part A: elaboration facts used by the audit.
Part B: `decouple`. The phase clauses of `Reconstructed` (`normalized`, `fullSupport`,
`characterContinuity`, `mixture`) do not tie the unselected (Wilson) slot `correlation none`
to the selected (Wightman) phase. From any hierarchy satisfying `Reconstructed` and ANY smooth,
permutation-symmetric prescription `W`, a two-character hierarchy over the SAME Wilson family
satisfies `Reconstructed`, keeps the Wightman theory, continuation and selected phase, and has
`correlation none = W`. -/

set_option autoImplicit false
noncomputable section

namespace YMAuditBridge
open YangMills MeasureTheory Filter Topology Set
open scoped ContDiff

/-! ### Part A -/

/-- `smooth` is C^∞ (not analytic): the projection typechecks at `((⊤ : ℕ∞) : WithTop ℕ∞)`. -/
example {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) (h : T.Reconstructed)
    (s : Option T.Character) {n : ℕ} (a : Fin n → T.Tag) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (T.correlation s a) (WilsonFamily.separated n) :=
  h.smooth s a

example : (∞ : WithTop ℕ∞) ≠ (⊤ : WithTop ℕ∞) := WithTop.coe_ne_top

/-- For one insertion the ordered tube is all of `ℂ`: the one-point continuation is entire. -/
example : Hierarchy.orderedTube 1 = Set.univ :=
  Set.eq_univ_of_forall fun z => by
    simp only [Hierarchy.orderedTube, Set.mem_setOf_eq]
    exact Subsingleton.strictMono _

/-- Time-ordered Euclidean configurations land in the tube (the `root` hypothesis). -/
example {n : ℕ} (x : Points n) (h : StrictMono fun i => time (x i)) :
    Hierarchy.imaginaryTimes x ∈ Hierarchy.orderedTube n := by
  simp only [Hierarchy.orderedTube, Hierarchy.imaginaryTimes, Set.mem_setOf_eq,
    Complex.mul_I_im, Complex.ofReal_re]
  exact h

/-- Shifted real configurations land in the tube for every `r > 0`. -/
example {n : ℕ} (r : ℝ) (hr : 0 < r) (height : Fin n → ℝ) (h : StrictMono height)
    (x : Points n) : Hierarchy.complexShift r height x ∈ Hierarchy.orderedTube n := by
  simp only [Hierarchy.orderedTube, Hierarchy.complexShift, Set.mem_setOf_eq,
    Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  exact fun i j hij => mul_lt_mul_of_pos_left (h hij) hr

/-- The `volume` used by `boundary` on `Points 0` has total mass one. -/
example : (volume : Measure (Points 0)) Set.univ = 1 := by
  have huniv : parallelepiped (stdOrthonormalBasis ℝ (Points 0)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x = 0 := PiLp.ext fun i => i.elim0
    rw [hx, mem_parallelepiped_iff]
    exact ⟨0, Set.left_mem_Icc.2 zero_le_one, by simp⟩
  rw [← huniv]
  exact (stdOrthonormalBasis ℝ (Points 0)).volume_parallelepiped

/-! ### Part B -/

/-- Two characters, as a subtype of `ℝ` (Mathlib supplies metric, Borel, compact instances). -/
abbrev Two : Type := ↥({0, 1} : Set ℝ)

def c0 : Two := ⟨0, by simp⟩
def c1 : Two := ⟨1, by simp⟩

/-- The uniform probability measure on the two characters. -/
def half : Measure Two := (2⁻¹ : ENNReal) • (Measure.dirac c0 + Measure.dirac c1)

theorem c1_ne_c0 : c1 ≠ c0 := by
  intro h
  have h' := congrArg Subtype.val h
  simp [c0, c1] at h'

theorem two_cases (p : Two) : p = c0 ∨ p = c1 := by
  obtain ⟨v, hv⟩ := p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem half_prob : IsProbabilityMeasure half := by
  constructor
  simp only [half, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

theorem half_openPos : half.IsOpenPosMeasure := by
  refine ⟨fun U _ hne => ?_⟩
  obtain ⟨p, hp⟩ := hne
  simp only [half, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  refine mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) ?_
  rcases two_cases p with rfl | rfl
  · rw [Measure.dirac_apply_of_mem hp]; simp
  · rw [Measure.dirac_apply_of_mem hp]; simp

variable {g : GaugeGroup} {C : WilsonFamily g}

open Classical in
/-- Character `c0` carries the selected phase `S` of `T₀`; character `c1` carries the
compensator `2W - S`; the unselected slot is `W`. -/
def decCorr (T₀ : Hierarchy C) (W : (n : ℕ) → (Fin n → T₀.Tag) → Points n → ℂ) {n : ℕ} :
    Option Two → (Fin n → T₀.Tag) → Points n → ℂ
  | none, a, x => W n a x
  | some i, a, x => if i = c0 then T₀.correlation (some T₀.selected) a x
      else 2 * W n a x - T₀.correlation (some T₀.selected) a x

/-- The decoupled hierarchy over the same Wilson family `C`. -/
def decouple (T₀ : Hierarchy C) (W : (n : ℕ) → (Fin n → T₀.Tag) → Points n → ℂ) :
    Hierarchy C where
  H := T₀.H
  labels := T₀.labels
  theory := T₀.theory
  Field := T₀.Field
  toLabel := T₀.toLabel
  project := T₀.project
  Character := Two
  phaseMeasure := half
  selected := c0
  correlation := decCorr T₀ W
  continuation := T₀.continuation
  Channel := T₀.Channel
  actor := T₀.actor
  coefficient := T₀.coefficient
  centeredTrace := T₀.centeredTrace

section
variable (T₀ : Hierarchy C) (W : (n : ℕ) → (Fin n → T₀.Tag) → Points n → ℂ)

theorem decCorr_c0 {n : ℕ} (a : Fin n → T₀.Tag) (x : Points n) :
    decCorr T₀ W (some c0) a x = T₀.correlation (some T₀.selected) a x :=
  if_pos rfl

theorem decCorr_ne {n : ℕ} {i : Two} (hi : i ≠ c0) (a : Fin n → T₀.Tag) (x : Points n) :
    decCorr T₀ W (some i) a x = 2 * W n a x - T₀.correlation (some T₀.selected) a x :=
  if_neg hi

theorem decCorr_continuous {n : ℕ} (a : Fin n → T₀.Tag) (x : Points n) :
    Continuous (fun i : Two => decCorr T₀ W (some i) a x) :=
  continuous_of_discreteTopology

theorem decCorr_mixture {n : ℕ} (a : Fin n → T₀.Tag) (x : Points n) :
    ∫ i : Two, decCorr T₀ W (some i) a x ∂half = W n a x := by
  have hi0 : Integrable (fun i : Two => decCorr T₀ W (some i) a x) (Measure.dirac c0) :=
    Integrable.of_finite
  have hi1 : Integrable (fun i : Two => decCorr T₀ W (some i) a x) (Measure.dirac c1) :=
    Integrable.of_finite
  rw [half, integral_smul_measure, integral_add_measure hi0 hi1, integral_dirac,
    integral_dirac]
  simp only [decCorr_c0, decCorr_ne T₀ W c1_ne_c0, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, Complex.real_smul]
  push_cast
  ring

theorem decouple_reconstructed (hR : T₀.Reconstructed)
    (hWs : ∀ (n : ℕ) (a : Fin n → T₀.Tag), ContDiffOn ℝ ∞ (W n a) (WilsonFamily.separated n))
    (hWp : ∀ (n : ℕ) (a : Fin n → T₀.Tag) (x : Points n), x ∈ WilsonFamily.separated n →
      ∀ π : Equiv.Perm (Fin n), W n (a ∘ π) (WithLp.toLp 2 (x.ofLp ∘ π)) = W n a x) :
    (decouple T₀ W).Reconstructed where
  axioms := hR.axioms
  faithful := hR.faithful
  injective := hR.injective
  acts := hR.acts
  covers := hR.covers
  represents := hR.represents
  normalized := half_prob
  fullSupport := half_openPos
  permutation := fun s {n} a x hx π => by
    cases s with
    | none => exact hWp n a x hx π
    | some i =>
      rcases two_cases i with rfl | rfl
      · show decCorr T₀ W (some c0) (a ∘ π) _ = decCorr T₀ W (some c0) a x
        rw [decCorr_c0, decCorr_c0]
        exact hR.permutation (some T₀.selected) a x hx π
      · show decCorr T₀ W (some c1) (a ∘ π) _ = decCorr T₀ W (some c1) a x
        rw [decCorr_ne T₀ W c1_ne_c0, decCorr_ne T₀ W c1_ne_c0,
          hR.permutation (some T₀.selected) a x hx π, hWp n a x hx π]
  smooth := fun s {n} a => by
    cases s with
    | none => exact hWs n a
    | some i =>
      by_cases hi : i = c0
      · subst hi
        exact (hR.smooth (some T₀.selected) a).congr fun x _ => decCorr_c0 T₀ W a x
      · exact (((contDiffOn_const (c := (2 : ℂ))).mul (hWs n a)).sub
          (hR.smooth (some T₀.selected) a)).congr fun x _ => decCorr_ne T₀ W hi a x
  characterContinuity := fun {n} a x _ => decCorr_continuous T₀ W a x
  mixture := fun {n} a x _ => decCorr_mixture T₀ W a x
  analytic := hR.analytic
  root := fun {n} v x h => (hR.root v x h).trans (decCorr_c0 T₀ W v x).symm
  boundary := hR.boundary

/-- The prescription of a theory with no nontrivial correlations: `1` on the empty word,
`0` on every nonempty word, at every point. -/
def vacuumOnly : (n : ℕ) → (Fin n → T₀.Tag) → Points n → ℂ :=
  fun n _ _ => if n = 0 then 1 else 0

/-- Headline: `Reconstructed` constrains the unselected slot only through `smooth` and
`permutation`. Here it is replaced by `vacuumOnly`, keeping theory and selected phase. -/
theorem reconstructed_unselected_free (hR : T₀.Reconstructed) :
    (decouple T₀ (vacuumOnly T₀)).Reconstructed ∧
    (∀ {n : ℕ} (a : Fin n → T₀.Tag) (x : Points n),
      (decouple T₀ (vacuumOnly T₀)).correlation none a x = if n = 0 then 1 else 0) ∧
    (∀ {n : ℕ} (a : Fin n → T₀.Tag) (x : Points n),
      (decouple T₀ (vacuumOnly T₀)).correlation
        (some (decouple T₀ (vacuumOnly T₀)).selected) a x =
        T₀.correlation (some T₀.selected) a x) ∧
    (decouple T₀ (vacuumOnly T₀)).theory = T₀.theory :=
  ⟨decouple_reconstructed T₀ _ hR (fun _ _ => contDiffOn_const) (fun _ _ _ _ _ => rfl),
    fun _ _ => rfl, fun a x => decCorr_c0 T₀ (vacuumOnly T₀) a x, rfl⟩

/-- The trace two-point function only reads the selected phase. -/
theorem decouple_traceTwo (r : ℝ) : (decouple T₀ W).traceTwo r = T₀.traceTwo r :=
  decCorr_c0 T₀ W (fun _ : Fin 2 => ⟨4, T₀.centeredTrace⟩) (Hierarchy.timePair r)

/-- `TraceTest` is preserved: among the continuum clauses only `ope` reads the other phases. -/
theorem decouple_traceTest (hT : T₀.TraceTest) : (decouple T₀ W).TraceTest where
  centered := hT.centered
  amplitudePositive := hT.amplitudePositive
  shortDistance := by
    have h : (decouple T₀ W).traceTwo = T₀.traceTwo := funext (decouple_traceTwo T₀ W)
    rw [h]
    exact hT.shortDistance
  excludes := fun terms => by
    have h : (decouple T₀ W).traceTwo = T₀.traceTwo := funext (decouple_traceTwo T₀ W)
    rw [h]
    exact hT.excludes terms

end

#print axioms decouple_reconstructed
#print axioms reconstructed_unselected_free
#print axioms decouple_traceTest

end YMAuditBridge
