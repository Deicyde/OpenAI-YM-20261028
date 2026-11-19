import ChallengeSpec

/-! Audit probe for the Hierarchy-data / OPE group (`ChallengeSpec.lean` lines 24-80).

A. `antiPhase T₀`: from any hierarchy `T₀`, a two-character hierarchy (characters `{0,1} ⊆ ℝ`,
   uniform measure) whose unselected (`none`) correlation is the *nonlinear* indicator
   `allZero` of the zero tag, whose selected phase is `T₀`'s selected phase `S`, and whose
   other phase is `2·allZero − S`. It inherits `OperatorProductExpansion` from `T₀`'s
   selected-phase OPE, using `T₀`'s coefficients plus one zero-actor channel per grade.
   The phase measure is a full-support probability measure whose average is `none`.
B. `zeroed T₀`: empty channels and identically-zero correlations satisfy the OPE clause.
-/

set_option autoImplicit false
noncomputable section

namespace YMAuditHierOPE
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

/-! ### Zero-tag indicator -/

/-- The zero vector of grade `0`, viewed as a tag. -/
def zeroTag (F : ℕ → Type) [∀ d, Zero (F d)] : Σ d, F d := ⟨0, 0⟩

open Classical in
/-- `1` if every entry is the zero tag (so `1` on the empty word), else `0`. -/
def allZero {F : ℕ → Type} [∀ d, Zero (F d)] {ι : Type} (w : ι → Σ d, F d) : ℂ :=
  if ∀ i, w i = zeroTag F then 1 else 0

theorem allZero_comp_equiv {F : ℕ → Type} [∀ d, Zero (F d)] {ι κ : Type}
    (w : ι → Σ d, F d) (e : κ ≃ ι) : allZero (w ∘ e) = allZero w := by
  unfold allZero
  by_cases h : ∀ i, w i = zeroTag F
  · have h' : ∀ k, (w ∘ e) k = zeroTag F := fun k => h (e k)
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∀ k, (w ∘ e) k = zeroTag F := by
      intro h'
      apply h
      intro i
      have := h' (e.symm i)
      simpa using this
    rw [if_neg h, if_neg h']

theorem allZero_sumElim {F : ℕ → Type} [∀ d, Zero (F d)] {ι κ : Type}
    (a : ι → Σ d, F d) (b : κ → Σ d, F d) :
    allZero (Sum.elim a b) = allZero a * allZero b := by
  unfold allZero
  by_cases ha : ∀ i, a i = zeroTag F
  · by_cases hb : ∀ j, b j = zeroTag F
    · have hab : ∀ k, Sum.elim a b k = zeroTag F := by
        intro k
        cases k with
        | inl i => exact ha i
        | inr j => exact hb j
      rw [if_pos ha, if_pos hb, if_pos hab, mul_one]
    · have hab : ¬ ∀ k, Sum.elim a b k = zeroTag F := fun h => hb fun j => h (Sum.inr j)
      rw [if_pos ha, if_neg hb, if_neg hab, mul_zero]
  · have hab : ¬ ∀ k, Sum.elim a b k = zeroTag F := fun h => ha fun i => h (Sum.inl i)
    rw [if_neg ha, if_neg hab, zero_mul]

/-! ### Two characters -/

/-- Two characters, realised as `{0, 1} ⊆ ℝ`. -/
abbrev Phase : Type := ↥({0, 1} : Set ℝ)

def phase0 : Phase := ⟨0, by simp⟩
def phase1 : Phase := ⟨1, by simp⟩

/-- The uniform probability measure on the two characters. -/
def phaseMeasure : Measure Phase := (2⁻¹ : ℝ≥0∞) • (Measure.dirac phase0 + Measure.dirac phase1)

theorem phase1_ne_phase0 : phase1 ≠ phase0 := by
  intro h
  have h' := congrArg Subtype.val h
  simp [phase0, phase1] at h'

theorem phase_cases (p : Phase) : p = phase0 ∨ p = phase1 := by
  obtain ⟨v, hv⟩ := p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem phaseMeasure_isProbability : IsProbabilityMeasure phaseMeasure := by
  constructor
  simp only [phaseMeasure, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

theorem phaseMeasure_isOpenPos : phaseMeasure.IsOpenPosMeasure := by
  refine ⟨fun U _ hne => ?_⟩
  obtain ⟨p, hp⟩ := hne
  simp only [phaseMeasure, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  refine mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) ?_
  rcases phase_cases p with rfl | rfl
  · rw [Measure.dirac_apply_of_mem hp]
    simp
  · rw [Measure.dirac_apply_of_mem hp]
    simp

/-! ### A. The anti-phase hierarchy -/

variable {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)

/-- The selected phase gives correlation `0` to every word containing the zero tag
(automatic when correlations are linear in each field vector). -/
def ZeroInvisible : Prop :=
  ∀ (n : ℕ) (w : Fin n → T₀.Tag) (x : Points n), (∃ i, w i = zeroTag T₀.Field) →
    T₀.correlation (some T₀.selected) w x = 0

open Classical in
def antiCorrelation {n : ℕ} : Option Phase → (Fin n → T₀.Tag) → Points n → ℂ
  | none, w, _ => allZero w
  | some i, w, x =>
      if i = phase0 then T₀.correlation (some T₀.selected) w x
      else 2 * allZero w - T₀.correlation (some T₀.selected) w x

def antiActor (j : ℕ) : Option (T₀.Channel j) → T₀.Field j
  | none => 0
  | some i => T₀.actor j i

open Classical in
def antiCoefficient {I : Type} [Fintype I] (a : I → T₀.Tag) (j : ℕ) :
    Option (T₀.Channel j) → (I → Spacetime) → Spacetime → ℂ
  | none, _, _ => if j = 0 then allZero a else 0
  | some i, x, o => if (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field then 0
      else T₀.coefficient a j i x o

/-- Same Hilbert space, fields, Wightman theory, continuation and trace field as `T₀`;
two characters; one extra channel (zero actor) in every grade. -/
def antiPhase : Hierarchy C₀ where
  H := T₀.H
  labels := T₀.labels
  theory := T₀.theory
  Field := T₀.Field
  toLabel := T₀.toLabel
  project := T₀.project
  Character := Phase
  phaseMeasure := phaseMeasure
  selected := phase0
  correlation := antiCorrelation T₀
  continuation := T₀.continuation
  Channel j := Option (T₀.Channel j)
  actor := antiActor T₀
  coefficient a j := antiCoefficient T₀ a j
  centeredTrace := T₀.centeredTrace

/-! #### Unfolding lemmas -/

theorem coef_none_zero {I : Type} [Fintype I] (a : I → (antiPhase T₀).Tag) (x : I → Spacetime)
    (o : Spacetime) : (antiPhase T₀).coefficient a 0 none x o = allZero a := by
  -- `if 0 = 0 then _ else _` reduces by computation, so this is definitional.
  first
  | rfl
  | exact rfl
  | (show antiCoefficient T₀ a 0 none x o = allZero a
     simp only [antiCoefficient]
     all_goals exact rfl)

theorem coef_none_ne {I : Type} [Fintype I] (a : I → (antiPhase T₀).Tag) (j : ℕ) (hj : j ≠ 0)
    (x : I → Spacetime) (o : Spacetime) : (antiPhase T₀).coefficient a j none x o = 0 := by
  first
  | exact if_neg hj
  | (show antiCoefficient T₀ a j none x o = 0; exact if_neg hj)

theorem coef_some_zero {I : Type} [Fintype I] (a : I → (antiPhase T₀).Tag) (j : ℕ)
    (i : T₀.Channel j) (h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field)
    (x : I → Spacetime) (o : Spacetime) : (antiPhase T₀).coefficient a j (some i) x o = 0 := by
  first
  | exact if_pos h
  | (show antiCoefficient T₀ a j (some i) x o = 0; exact if_pos h)

theorem coef_some_ne {I : Type} [Fintype I] (a : I → (antiPhase T₀).Tag) (j : ℕ)
    (i : T₀.Channel j) (h : ¬ (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field)
    (x : I → Spacetime) (o : Spacetime) :
    (antiPhase T₀).coefficient a j (some i) x o = T₀.coefficient a j i x o := by
  first
  | exact if_neg h
  | (show antiCoefficient T₀ a j (some i) x o = T₀.coefficient a j i x o; exact if_neg h)

theorem allZero_actor_none_zero :
    allZero (fun _ : Unit => (⟨0, (antiPhase T₀).actor 0 none⟩ : (antiPhase T₀).Tag)) = 1 := by
  unfold allZero
  exact if_pos (fun _ => rfl)

theorem sum_channels (j : ℕ) (f : (antiPhase T₀).Channel j → ℂ) :
    ∑ i, f i = f none + ∑ i : T₀.Channel j, f (some i) :=
  Fintype.sum_option f

theorem term_some_allZero {I : Type} [Fintype I] (a : I → (antiPhase T₀).Tag)
    (x : I → Spacetime) (o : Spacetime) (j : ℕ) (i : T₀.Channel j) :
    (antiPhase T₀).coefficient a j (some i) x o *
      allZero (fun _ : Unit => (⟨j, (antiPhase T₀).actor j (some i)⟩ : (antiPhase T₀).Tag))
      = 0 := by
  by_cases h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field
  · rw [coef_some_zero T₀ a j i h x o, zero_mul]
  · have h2 : allZero (fun _ : Unit =>
        (⟨j, (antiPhase T₀).actor j (some i)⟩ : (antiPhase T₀).Tag)) = 0 := by
      unfold allZero
      exact if_neg (fun h' => h (h' ()))
    rw [h2, mul_zero]

/-- Grade-by-grade: the zero-tag indicator sees only the new grade-0 channel. -/
theorem innerA {I : Type} [Fintype I] (a : I → (antiPhase T₀).Tag) (x : I → Spacetime)
    (o : Spacetime) (j : ℕ) :
    (∑ i : (antiPhase T₀).Channel j, (antiPhase T₀).coefficient a j i x o *
        allZero (fun _ : Unit => (⟨j, (antiPhase T₀).actor j i⟩ : (antiPhase T₀).Tag)))
      = if j = 0 then allZero a else 0 := by
  rw [sum_channels T₀ j,
    Finset.sum_eq_zero (fun (i : T₀.Channel j) _ => term_some_allZero T₀ a x o j i), add_zero]
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, coef_none_zero T₀ a x o, allZero_actor_none_zero T₀, mul_one]
  · rw [if_neg hj, coef_none_ne T₀ a j hj x o, zero_mul]

theorem termB_none (hZ : ZeroInvisible T₀) {I J : Type} [Fintype I] [Fintype J]
    (a : I → (antiPhase T₀).Tag) (x : I → Spacetime) (o : Spacetime)
    (b : J → (antiPhase T₀).Tag) (y : J → Spacetime) (j : ℕ) :
    (antiPhase T₀).coefficient a j none x o *
      T₀.grouped (some T₀.selected)
        (fun _ : Unit => (⟨j, (antiPhase T₀).actor j none⟩ : (antiPhase T₀).Tag))
        (fun _ => o) b y = 0 := by
  by_cases hj : j = 0
  · subst hj
    have hz : T₀.grouped (some T₀.selected)
        (fun _ : Unit => (⟨0, (antiPhase T₀).actor 0 none⟩ : (antiPhase T₀).Tag))
        (fun _ => o) b y = 0 := by
      apply hZ
      refine ⟨(Fintype.equivFin (Unit ⊕ J)) (Sum.inl ()), ?_⟩
      have e : (Fintype.equivFin (Unit ⊕ J)).symm ((Fintype.equivFin (Unit ⊕ J)) (Sum.inl ())) =
          Sum.inl () := Equiv.symm_apply_apply _ _
      show Sum.elim (fun _ : Unit => (⟨0, (antiPhase T₀).actor 0 none⟩ : (antiPhase T₀).Tag)) b
          ((Fintype.equivFin (Unit ⊕ J)).symm ((Fintype.equivFin (Unit ⊕ J)) (Sum.inl ()))) =
            zeroTag T₀.Field
      rw [e]
      all_goals exact rfl
    rw [hz, mul_zero]
  · rw [coef_none_ne T₀ a j hj x o, zero_mul]

theorem termB_some (hZ : ZeroInvisible T₀) {I J : Type} [Fintype I] [Fintype J]
    (a : I → (antiPhase T₀).Tag) (x : I → Spacetime) (o : Spacetime)
    (b : J → (antiPhase T₀).Tag) (y : J → Spacetime) (j : ℕ) (i : T₀.Channel j) :
    (antiPhase T₀).coefficient a j (some i) x o *
      T₀.grouped (some T₀.selected)
        (fun _ : Unit => (⟨j, (antiPhase T₀).actor j (some i)⟩ : (antiPhase T₀).Tag))
        (fun _ => o) b y
    = T₀.coefficient a j i x o *
      T₀.grouped (some T₀.selected) (fun _ : Unit => (⟨j, T₀.actor j i⟩ : T₀.Tag))
        (fun _ => o) b y := by
  by_cases h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field
  · have hz : T₀.grouped (some T₀.selected) (fun _ : Unit => (⟨j, T₀.actor j i⟩ : T₀.Tag))
        (fun _ => o) b y = 0 := by
      apply hZ
      refine ⟨(Fintype.equivFin (Unit ⊕ J)) (Sum.inl ()), ?_⟩
      have e : (Fintype.equivFin (Unit ⊕ J)).symm ((Fintype.equivFin (Unit ⊕ J)) (Sum.inl ())) =
          Sum.inl () := Equiv.symm_apply_apply _ _
      show Sum.elim (fun _ : Unit => (⟨j, T₀.actor j i⟩ : T₀.Tag)) b
          ((Fintype.equivFin (Unit ⊕ J)).symm ((Fintype.equivFin (Unit ⊕ J)) (Sum.inl ()))) =
            zeroTag T₀.Field
      rw [e]
      exact h
    rw [coef_some_zero T₀ a j i h x o, hz, zero_mul, mul_zero]
  · rw [coef_some_ne T₀ a j i h x o]
    all_goals exact rfl

/-- Grade-by-grade: in the selected phase the extra channel contributes nothing and the
zeroed-out channels contributed nothing in `T₀` either. -/
theorem innerB (hZ : ZeroInvisible T₀) {I J : Type} [Fintype I] [Fintype J]
    (a : I → (antiPhase T₀).Tag) (x : I → Spacetime) (o : Spacetime)
    (b : J → (antiPhase T₀).Tag) (y : J → Spacetime) (j : ℕ) :
    (∑ i : (antiPhase T₀).Channel j, (antiPhase T₀).coefficient a j i x o *
        T₀.grouped (some T₀.selected)
          (fun _ : Unit => (⟨j, (antiPhase T₀).actor j i⟩ : (antiPhase T₀).Tag)) (fun _ => o) b y)
      = ∑ i : T₀.Channel j, T₀.coefficient a j i x o *
          T₀.grouped (some T₀.selected) (fun _ : Unit => (⟨j, T₀.actor j i⟩ : T₀.Tag))
            (fun _ => o) b y := by
  rw [sum_channels T₀ j, termB_none T₀ hZ a x o b y j, zero_add]
  exact Finset.sum_congr rfl (fun i _ => termB_some T₀ hZ a x o b y j i)

open Classical in
/-- Weight of the zero-tag indicator in each phase. -/
def phaseA : Option Phase → ℂ
  | none => 1
  | some p => if p = phase0 then 0 else 2

open Classical in
/-- Weight of the selected correlation in each phase. -/
def phaseK : Option Phase → ℂ
  | none => 0
  | some p => if p = phase0 then 1 else -1

/-- Every phase of the anti-phase hierarchy is `phaseA s · allZero + phaseK s · S`. -/
theorem anti_grouped_lin (s : Option Phase) {I J : Type} [Fintype I] [Fintype J]
    (a : I → (antiPhase T₀).Tag) (x : I → Spacetime) (b : J → (antiPhase T₀).Tag)
    (y : J → Spacetime) :
    (antiPhase T₀).grouped s a x b y =
      phaseA s * (allZero a * allZero b) + phaseK s * T₀.grouped (some T₀.selected) a x b y := by
  cases s with
  | none =>
    have h1 : (antiPhase T₀).grouped (none : Option Phase) a x b y =
        allZero ((Sum.elim a b) ∘ (Fintype.equivFin (I ⊕ J)).symm) := rfl
    have hA : phaseA none = 1 := rfl
    have hK : phaseK none = 0 := rfl
    rw [h1, allZero_comp_equiv, allZero_sumElim, hA, hK]
    ring
  | some p =>
    by_cases hp : p = phase0
    · have h1 : (antiPhase T₀).grouped (some p : Option Phase) a x b y =
          T₀.grouped (some T₀.selected) a x b y := if_pos hp
      have hA : phaseA (some p) = 0 := if_pos hp
      have hK : phaseK (some p) = 1 := if_pos hp
      rw [h1, hA, hK]
      ring
    · have h1 : (antiPhase T₀).grouped (some p : Option Phase) a x b y =
          2 * allZero ((Sum.elim a b) ∘ (Fintype.equivFin (I ⊕ J)).symm) -
            T₀.grouped (some T₀.selected) a x b y := if_neg hp
      have hA : phaseA (some p) = 2 := if_neg hp
      have hK : phaseK (some p) = -1 := if_neg hp
      rw [h1, allZero_comp_equiv, allZero_sumElim, hA, hK]
      ring

theorem norm_phaseK_le (s : Option Phase) : ‖phaseK s‖ ≤ 1 := by
  cases s with
  | none =>
    have h : phaseK none = 0 := rfl
    rw [h, norm_zero]
    exact zero_le_one
  | some p =>
    by_cases hp : p = phase0
    · have h : phaseK (some p) = 1 := if_pos hp
      rw [h, norm_one]
    · have h : phaseK (some p) = -1 := if_neg hp
      rw [h, norm_neg, norm_one]

theorem sum_ite_val_zero (D : ℕ) (z : ℂ) :
    (∑ j : Fin (D+1), (if j.val = 0 then z else 0)) = z := by
  rw [Fin.sum_univ_succ]
  have h1 : ∀ i : Fin D, (if (Fin.succ i).val = 0 then z else 0) = 0 :=
    fun i => if_neg (Nat.succ_ne_zero _)
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const_zero, add_zero]
  first
  | exact if_pos rfl
  | simp

/-- `T₀`'s OPE remainder in its selected phase. -/
def rem0 {I J : Type} [Fintype I] [Fintype J] (a : I → T₀.Tag) (x : I → Spacetime)
    (o : Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) (D : ℕ) : ℂ :=
  T₀.grouped (some T₀.selected) a x b y -
    ∑ j : Fin (D+1), ∑ i : T₀.Channel j.val, T₀.coefficient a j.val i x o *
      T₀.grouped (some T₀.selected) (fun _ : Unit => ⟨j.val, T₀.actor j.val i⟩) (fun _ => o) b y

/-- The anti-phase hierarchy's OPE remainder in phase `s`. -/
def remAnti (s : Option Phase) {I J : Type} [Fintype I] [Fintype J]
    (a : I → (antiPhase T₀).Tag) (x : I → Spacetime) (o : Spacetime)
    (b : J → (antiPhase T₀).Tag) (y : J → Spacetime) (D : ℕ) : ℂ :=
  (antiPhase T₀).grouped s a x b y -
    ∑ j : Fin (D+1), ∑ i : (antiPhase T₀).Channel j.val, (antiPhase T₀).coefficient a j.val i x o *
      (antiPhase T₀).grouped s (fun _ : Unit => ⟨j.val, (antiPhase T₀).actor j.val i⟩)
        (fun _ => o) b y

/-- In every phase the anti-phase remainder is `0`, `+` or `−` the selected `T₀` remainder. -/
theorem remAnti_eq (hZ : ZeroInvisible T₀) (s : Option Phase) {I J : Type} [Fintype I]
    [Fintype J] (a : I → (antiPhase T₀).Tag) (x : I → Spacetime) (o : Spacetime)
    (b : J → (antiPhase T₀).Tag) (y : J → Spacetime) (D : ℕ) :
    remAnti T₀ s a x o b y D = phaseK s * rem0 T₀ a x o b y D := by
  have step : ∀ j : Fin (D+1),
      (∑ i : (antiPhase T₀).Channel j.val, (antiPhase T₀).coefficient a j.val i x o *
        (antiPhase T₀).grouped s (fun _ : Unit => ⟨j.val, (antiPhase T₀).actor j.val i⟩)
          (fun _ => o) b y)
      = phaseA s * allZero b * (if j.val = 0 then allZero a else 0) +
        phaseK s * ∑ i : T₀.Channel j.val, T₀.coefficient a j.val i x o *
          T₀.grouped (some T₀.selected) (fun _ : Unit => (⟨j.val, T₀.actor j.val i⟩ : T₀.Tag))
            (fun _ => o) b y := by
    intro j
    rw [← innerA T₀ a x o j.val, ← innerB T₀ hZ a x o b y j.val, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [anti_grouped_lin T₀ s]
    ring
  have hsum : (∑ j : Fin (D+1), ∑ i : (antiPhase T₀).Channel j.val,
        (antiPhase T₀).coefficient a j.val i x o *
          (antiPhase T₀).grouped s (fun _ : Unit => ⟨j.val, (antiPhase T₀).actor j.val i⟩)
            (fun _ => o) b y)
      = phaseA s * allZero b * allZero a + phaseK s * ∑ j : Fin (D+1), ∑ i : T₀.Channel j.val,
          T₀.coefficient a j.val i x o * T₀.grouped (some T₀.selected)
            (fun _ : Unit => (⟨j.val, T₀.actor j.val i⟩ : T₀.Tag)) (fun _ => o) b y := by
    rw [Finset.sum_congr rfl (fun j _ => step j), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_ite_val_zero]
  unfold remAnti rem0
  rw [hsum, anti_grouped_lin T₀ s a x b y]
  ring

/-- **The anti-phase hierarchy satisfies the public OPE** whenever `T₀` does (only `T₀`'s
selected phase is used) and `T₀`'s selected phase ignores the zero tag. -/
theorem antiPhase_ope (hO : T₀.OperatorProductExpansion) (hZ : ZeroInvisible T₀) :
    (antiPhase T₀).OperatorProductExpansion := by
  constructor
  · intro I _ a M η ε hM hη hε j i
    change Option (T₀.Channel j) at i
    cases i with
    | none =>
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with r hr x o _
      have hr0 : 0 < r := hr.1
      by_cases hj : j = 0
      · subst hj
        by_cases ha : ∀ k, a k = zeroTag T₀.Field
        · have hw : T₀.weight a = 0 := by
            unfold Hierarchy.weight
            refine Finset.sum_eq_zero (fun k _ => ?_)
            rw [ha k]
            exact Nat.cast_zero
          have hc : (antiPhase T₀).coefficient a 0 none x o = 1 := by
            rw [coef_none_zero T₀ a x o]
            unfold allZero
            exact if_pos ha
          rw [hc, norm_one]
          show 1 ≤ r ^ (((0:ℕ):ℝ) - T₀.weight a - ε)
          rw [hw]
          apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr.2.le
          have h0 : ((0:ℕ):ℝ) = 0 := Nat.cast_zero
          linarith
        · have hc : (antiPhase T₀).coefficient a 0 none x o = 0 := by
            rw [coef_none_zero T₀ a x o]
            unfold allZero
            exact if_neg ha
          rw [hc, norm_zero]
          exact Real.rpow_nonneg hr0.le _
      · rw [coef_none_ne T₀ a j hj x o, norm_zero]
        exact Real.rpow_nonneg hr0.le _
    | some i =>
      filter_upwards [self_mem_nhdsWithin, hO.coefficients a M η ε hM hη hε j i]
        with r hr0 hr x o hx
      by_cases h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field
      · rw [coef_some_zero T₀ a j i h x o, norm_zero]
        exact Real.rpow_nonneg (le_of_lt (Set.mem_Ioi.mp hr0)) _
      · rw [coef_some_ne T₀ a j i h x o]
        exact hr x o hx
  · intro I J _ _ a b M η c ε hM hη hc hε D
    filter_upwards [hO.remainder a b M η c ε hM hη hc hε D] with r hr
    intro x o y hx hy s
    have key := hr x o y hx hy (some T₀.selected)
    have e1 : ‖remAnti T₀ s a x o b y D‖ ≤ r ^ ((D:ℝ) + 1 - T₀.weight a - ε) := by
      rw [remAnti_eq T₀ hZ s a x o b y D, norm_mul]
      calc ‖phaseK s‖ * ‖rem0 T₀ a x o b y D‖ ≤ 1 * ‖rem0 T₀ a x o b y D‖ :=
            mul_le_mul_of_nonneg_right (norm_phaseK_le s) (norm_nonneg _)
        _ = ‖rem0 T₀ a x o b y D‖ := one_mul _
        _ ≤ r ^ ((D:ℝ) + 1 - T₀.weight a - ε) := key
    exact e1

/-! #### Character data of the anti-phase hierarchy -/

theorem anti_phase0 {n : ℕ} (w : Fin n → T₀.Tag) (x : Points n) :
    antiCorrelation T₀ (some phase0) w x = T₀.correlation (some T₀.selected) w x := if_pos rfl

theorem anti_phase1 {n : ℕ} (w : Fin n → T₀.Tag) (x : Points n) :
    antiCorrelation T₀ (some phase1) w x =
      2 * allZero w - T₀.correlation (some T₀.selected) w x :=
  if_neg phase1_ne_phase0

/-- Averaging the two characters gives the nonlinear indicator `allZero`. -/
theorem antiPhase_mixture {n : ℕ} (w : Fin n → T₀.Tag) (x : Points n) :
    (∫ i, antiCorrelation T₀ (some i) w x ∂phaseMeasure) = antiCorrelation T₀ none w x := by
  have hi0 : Integrable (fun i : Phase => antiCorrelation T₀ (some i) w x)
      (Measure.dirac phase0) := Integrable.of_finite
  have hi1 : Integrable (fun i : Phase => antiCorrelation T₀ (some i) w x)
      (Measure.dirac phase1) := Integrable.of_finite
  rw [phaseMeasure, integral_smul_measure, integral_add_measure hi0 hi1, integral_dirac,
    integral_dirac, anti_phase0, anti_phase1]
  show (2⁻¹ : ℝ≥0∞).toReal • (T₀.correlation (some T₀.selected) w x +
      (2 * allZero w - T₀.correlation (some T₀.selected) w x)) = allZero w
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat, Complex.real_smul]
  push_cast
  ring

/-- The anti-phase hierarchy's selected correlation is literally `T₀`'s. -/
theorem antiPhase_selected {n : ℕ} (w : Fin n → T₀.Tag) (x : Points n) :
    (antiPhase T₀).correlation (some (antiPhase T₀).selected) w x =
      T₀.correlation (some T₀.selected) w x := if_pos rfl

/-! ### B. Empty channels and zero correlations satisfy the OPE clause by themselves -/

def zeroed : Hierarchy C₀ where
  H := T₀.H
  labels := T₀.labels
  theory := T₀.theory
  Field := T₀.Field
  toLabel := T₀.toLabel
  project := T₀.project
  Character := T₀.Character
  phaseMeasure := T₀.phaseMeasure
  selected := T₀.selected
  correlation := fun _ _ _ => 0
  continuation := T₀.continuation
  Channel := fun _ => Empty
  finiteChannels := fun _ => (inferInstance : Fintype Empty)
  actor := fun _ e => Empty.elim e
  coefficient := fun _ _ e => Empty.elim e
  centeredTrace := T₀.centeredTrace

theorem zeroed_ope : (zeroed T₀).OperatorProductExpansion := by
  constructor
  · intro I _ a M η ε hM hη hε j i
    exact Empty.elim i
  · intro I J _ _ a b M η c ε hM hη hc hε D
    filter_upwards [self_mem_nhdsWithin] with r hr
    intro x o y _ _ s
    have hg : ∀ {I' J' : Type} [Fintype I'] [Fintype J'] (s' : Option (zeroed T₀).Character)
        (a' : I' → (zeroed T₀).Tag) (x' : I' → Spacetime) (b' : J' → (zeroed T₀).Tag)
        (y' : J' → Spacetime), (zeroed T₀).grouped s' a' x' b' y' = 0 :=
      fun _ _ _ _ _ => rfl
    simp only [hg, mul_zero, Finset.sum_const_zero, sub_zero, norm_zero]
    exact Real.rpow_nonneg (le_of_lt (Set.mem_Ioi.mp hr)) _

#print axioms antiPhase_ope
#print axioms antiPhase_mixture
#print axioms phaseMeasure_isProbability
#print axioms phaseMeasure_isOpenPos
#print axioms zeroed_ope

end YMAuditHierOPE
