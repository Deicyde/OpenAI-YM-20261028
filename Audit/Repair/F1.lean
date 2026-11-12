import ChallengeSpec
import Audit.Reduction.Defs

/-!
# Repair F1: reconstruction at every character (audit, not part of the submission)

`Hierarchy.Reconstructed` asks for a Wightman theory, a continuation and its boundary values only
at the selected character. Repair F1 (`AUDIT.md`, "What would close it") asks for them at every
character. `CharacterReconstruction T i` is that data at `i`: a Wightman theory over the
hierarchy's labels and a continuation, with the clauses `axioms`, `faithful`, `acts`, `analytic`,
`root` and `boundary` of `Reconstructed` read at `i`. `JointExistenceF1` is `JointExistence` with
such data at every character.

`reduced_not_perCharacter`: the reduction of `Audit/Reduction` fails the repair. Its second phase,
`2 · allZero − S`, is the constant `2` on the one-point word of the zero tag, while data at any
character force a constant one-point correlation of the zero tag to be `0` (`zeroWord_const`, the
argument of `AuditScripts/Probes/reconbridge_perphase.lean`).
-/

set_option autoImplicit false
noncomputable section

namespace YMAudit.F1
open YangMills MeasureTheory Filter Topology Set
open scoped ContDiff

variable {g : GaugeGroup} {C : WilsonFamily g}

/-- Reconstruction data at the character `i`: the clauses of `Reconstructed` about the Wightman
theory and the continuation, read at `i` instead of the selected character. -/
structure CharacterReconstruction (T : Hierarchy C) (i : T.Character) where
  H : YangMills.HilbertSpace
  theory : WightmanTheory H T.labels
  continuation {n : ℕ} : (Fin n → T.Tag) → (Fin n → ℂ) → (Fin n → Space) → ℂ
  axioms : theory.Axioms
  faithful : theory.fields.Faithful
  acts : ∃ (a : T.Tag) (f : YangMills.TestFunction),
    theory.fields.field (T.toLabel a.1 a.2) f ≠ 0
  analytic {n : ℕ} (v : Fin n → T.Tag) (space : Hierarchy.OPESpacePoints n) :
    DifferentiableOn ℂ (fun z => continuation v z space) (Hierarchy.orderedTube n)
  root {n : ℕ} (v : Fin n → T.Tag) (x : Points n) (h : StrictMono fun k => time (x k)) :
    continuation v (Hierarchy.imaginaryTimes x) (Hierarchy.spatialPoints x) =
      T.correlation (some i) v x
  boundary {n : ℕ} (v : Fin n → T.Tag) (height : Fin n → ℝ) (h : StrictMono height)
      (tests : Fin n → YangMills.TestFunction) :
    Tendsto (fun r => ∫ x : Points n, continuation v (Hierarchy.complexShift r height x)
      (Hierarchy.spatialPoints x) * Hierarchy.tensorTest tests x) (𝓝[>] 0)
      (𝓝 (theory.fields.vacuumExpectation (fun k => T.toLabel (v k).1 (v k).2) tests))

/-- Repair F1: reconstruction data at every character. -/
def PerCharacter (T : Hierarchy C) : Prop :=
  ∀ i : T.Character, Nonempty (CharacterReconstruction T i)

/-- `JointExistence` with reconstruction data at every character of the hierarchy. -/
def JointExistenceF1 : Prop := ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
  WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ PerCharacter T

/-- The repair only adds a clause. -/
theorem jointExistence_of_F1 (h : JointExistenceF1) : JointExistence := by
  intro g hg
  obtain ⟨C, hC, hp⟩ := h g hg
  refine ⟨C, hC, fun p hp' => ?_⟩
  obtain ⟨q, hq, T, hT, -⟩ := hp p hp'
  exact ⟨q, hq, T, hT⟩

/-- At the selected character, `Reconstructed` supplies the data. -/
def CharacterReconstruction.ofReconstructed (T : Hierarchy C) (h : T.Reconstructed) :
    CharacterReconstruction T T.selected where
  H := T.H
  theory := T.theory
  continuation := T.continuation
  axioms := h.axioms
  faithful := h.faithful
  acts := h.acts
  analytic := h.analytic
  root := h.root
  boundary := h.boundary

/-! ### A constant one-point correlation of the zero tag vanishes -/

theorem orderedTube_one : Hierarchy.orderedTube 1 = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  show StrictMono fun i : Fin 1 => (z i).im
  intro a b hab
  exact absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl b)

theorem vector_eq_zero {H : YangMills.HilbertSpace} {L : FieldLabels} (F : FieldSystem H L)
    (w : List (L.carrier × YangMills.TestFunction)) (h : ∃ p ∈ w, p.1 = 0) :
    F.vector w = 0 := by
  induction w with
  | nil => simp at h
  | cons q w ih =>
    show F.field q.1 q.2 (F.vector w) = 0
    by_cases hq : q.1 = 0
    · rw [hq, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
    · obtain ⟨p, hp, hp0⟩ := h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact absurd hp0 hq
      · rw [ih ⟨p, hp', hp0⟩, map_zero]

theorem vacuumExpectation_zero_label {H : YangMills.HilbertSpace} {L : FieldLabels}
    (F : FieldSystem H L) {n : ℕ} (labels : Fin n → L.carrier)
    (tests : Fin n → YangMills.TestFunction) (k : Fin n) (hk : labels k = 0) :
    F.vacuumExpectation labels tests = 0 := by
  unfold FieldSystem.vacuumExpectation
  rw [vector_eq_zero F (List.ofFn fun i => (labels i, tests i))
    ⟨(labels k, tests k), (List.mem_ofFn' _ _).mpr ⟨k, rfl⟩, hk⟩]
  simp

/-- A one-point configuration with prescribed spatial part and time. -/
def onePoint (s : Space) (t : ℝ) : Points 1 :=
  WithLp.toLp 2 fun _ => (WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) s.ofLp t) : Spacetime)

def bump : ContDiffBump (0 : Spacetime) := ⟨1, 2, one_pos, one_lt_two⟩

def bumpC : Spacetime → ℂ := fun y => ((bump y : ℝ) : ℂ)

theorem bumpC_smooth : ContDiff ℝ ∞ bumpC :=
  Complex.ofRealCLM.contDiff.comp bump.contDiff

theorem bumpC_support : HasCompactSupport bumpC :=
  bump.hasCompactSupport.comp_left Complex.ofReal_zero

/-- A Schwartz test with nonzero integral on `Points 1`. -/
def bumpTest : YangMills.TestFunction := bumpC_support.toSchwartzMap bumpC_smooth

theorem integral_bump_ne :
    (∫ x : Points 1, Hierarchy.tensorTest (fun _ => bumpTest) x) ≠ 0 := by
  have h1 : (fun x : Points 1 => Hierarchy.tensorTest (fun _ => bumpTest) x) =
      fun x => ((bump (x.ofLp 0) : ℝ) : ℂ) := by
    funext x
    simp only [Hierarchy.tensorTest, Fin.prod_univ_one]
    rfl
  rw [h1, integral_complex_ofReal]
  have hc : Continuous fun x : Points 1 => bump (x.ofLp 0) :=
    bump.continuous.comp (PiLp.continuous_apply _ _ 0)
  have hs : HasCompactSupport fun x : Points 1 => bump (x.ofLp 0) :=
    bump.hasCompactSupport.comp_homeomorph
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => Spacetime)).toHomeomorph
  have h0 : bump ((0 : Points 1).ofLp 0) ≠ 0 := by
    rw [show ((0 : Points 1).ofLp 0) = (0 : Spacetime) from rfl,
      bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)]
    exact one_ne_zero
  have hpos := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hs
    (fun x => bump.nonneg) h0
  exact_mod_cast hpos.ne'

/-- The one-point word of the zero tag. -/
def zeroWord (T : Hierarchy C) : Fin 1 → T.Tag := fun _ => zeroTag T.Field

/-- Reconstruction data at a character force a constant correlation of that character on the
one-point word of the zero tag to be `0`: the continuation is then that constant, and its
boundary values are the vacuum expectation of a zero field. -/
theorem zeroWord_const {T : Hierarchy C} {i : T.Character} (D : CharacterReconstruction T i)
    (c : ℂ) (hc : ∀ x : Points 1, T.correlation (some i) (zeroWord T) x = c) : c = 0 := by
  have hsm1 : ∀ f : Fin 1 → ℝ, StrictMono f := fun f a b hab =>
    absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl b)
  -- Step 1: the continuation is the constant `c` (identity theorem in one variable).
  have hconst : ∀ z sp, D.continuation (zeroWord T) z sp = c := by
    intro z sp
    have hdiff : Differentiable ℂ (fun z : Fin 1 → ℂ => D.continuation (zeroWord T) z sp) := by
      have h := D.analytic (zeroWord T) sp
      rw [orderedTube_one] at h
      exact differentiableOn_univ.mp h
    let G : ℂ → ℂ := fun w => D.continuation (zeroWord T) (fun _ => w) sp
    have hG : Differentiable ℂ G :=
      hdiff.comp (differentiable_pi.2 fun _ => differentiable_id)
    have hGa : AnalyticOnNhd ℂ G Set.univ := fun w _ => hG.analyticAt w
    have hroot : ∀ t : ℝ, G ((t : ℂ) * Complex.I) = c := by
      intro t
      have ht : ∀ k, time ((onePoint (sp 0) t).ofLp k) = t := fun k => by
        change Fin.snoc (α := fun _ => ℝ) (sp 0).ofLp t (Fin.last 3) = t
        exact Fin.snoc_last _ _
      have h1 : Hierarchy.imaginaryTimes (onePoint (sp 0) t) =
          fun _ => (t : ℂ) * Complex.I := by
        funext k
        simp only [Hierarchy.imaginaryTimes, ht]
      have h2 : Hierarchy.spatialPoints (onePoint (sp 0) t) = sp := by
        funext k
        rw [Subsingleton.elim k 0]
        simp [Hierarchy.spatialPoints, onePoint, YangMills.spatial, PiLp.toLp_apply]
      have := D.root (zeroWord T) (onePoint (sp 0) t) (hsm1 _)
      rw [h1, h2, hc] at this
      exact this
    have hu : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)) atTop
        (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h1 := ((Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h0).mul_const Complex.I
        rw [Complex.ofReal_zero, zero_mul] at h1
        exact h1
      · exact mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) Complex.I_ne_zero
    have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), G w = c :=
      hu.frequently (Frequently.of_forall fun n => hroot (1 / ((n : ℝ) + 1)))
    have hGc : G = fun _ => c := hGa.eq_of_frequently_eq analyticOnNhd_const hfreq
    have hz : z = fun _ => z 0 := funext fun k => by rw [Subsingleton.elim k 0]
    rw [hz]
    exact congrFun hGc (z 0)
  -- Step 2: the boundary integral is `c * ∫ tensorTest`, but the vacuum expectation of a word
  -- with a zero label vanishes.
  have hlim := D.boundary (zeroWord T) (fun _ => 0) (hsm1 _) (fun _ => bumpTest)
  have hint : ∀ r : ℝ, (∫ x : Points 1, D.continuation (zeroWord T)
      (Hierarchy.complexShift r (fun _ => 0) x) (Hierarchy.spatialPoints x) *
        Hierarchy.tensorTest (fun _ => bumpTest) x) =
      c * ∫ x : Points 1, Hierarchy.tensorTest (fun _ => bumpTest) x := by
    intro r
    simp_rw [hconst]
    exact integral_const_mul c _
  simp_rw [hint] at hlim
  have hzero : D.theory.fields.vacuumExpectation
      (fun k => T.toLabel (zeroWord T k).1 (zeroWord T k).2) (fun _ => bumpTest) = 0 :=
    vacuumExpectation_zero_label D.theory.fields _ _ 0 (by exact (T.toLabel 0).map_zero)
  rw [hzero] at hlim
  have heq : c * (∫ x : Points 1, Hierarchy.tensorTest (fun _ => bumpTest) x) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  exact (mul_eq_zero.mp heq).resolve_right integral_bump_ne

/-! ### The reduction fails the repair -/

theorem phase1_ne_phase0 : phase1 ≠ phase0 := by
  intro h
  have h' := congrArg Subtype.val h
  simp [phase0, phase1] at h'

/-- The second phase of the reduced hierarchy has no reconstruction data: on the one-point word
of the zero tag its correlation is `2 · 1 − 0 = 2`. -/
theorem reduced_phase1_isEmpty {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀) (hZ : ZeroInvisible T₀)
    (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure) :
    IsEmpty (CharacterReconstruction (reduced T₀ μ hH) phase1) := by
  refine ⟨fun D => ?_⟩
  have h2 : ∀ x : Points 1,
      (reduced T₀ μ hH).correlation (some phase1) (zeroWord (reduced T₀ μ hH)) x = 2 := by
    intro x
    show redCorrelation T₀ (some phase1) (fun _ => zeroTag T₀.Field) x = 2
    have hall : allZero (fun _ : Fin 1 => zeroTag T₀.Field) = 1 := by
      unfold allZero
      exact if_pos fun _ => rfl
    have hS : T₀.correlation (some T₀.selected) (fun _ : Fin 1 => zeroTag T₀.Field) x = 0 :=
      hZ 1 _ x ⟨0, rfl⟩
    simp only [redCorrelation, if_neg phase1_ne_phase0, hall, hS, mul_one, sub_zero]
  have h := zeroWord_const D 2 h2
  norm_num at h

/-- The reduced hierarchy fails repair F1. -/
theorem reduced_not_perCharacter {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (hZ : ZeroInvisible T₀) (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) : ¬ PerCharacter (reduced T₀ μ hH) := fun h =>
  (reduced_phase1_isEmpty T₀ hZ μ hH).false (h phase1).some

end YMAudit.F1
