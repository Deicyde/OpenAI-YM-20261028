import ChallengeSpec

/-!
# Shared definitions for the reduction (audit, not part of the submission)

From any hierarchy `T₀` (over any Wilson family) satisfying the three continuum clauses
`Reconstructed`, `OperatorProductExpansion` and `TraceTest`, plus zero-tag invisibility in its
selected phase, we build a gauge-blind Wilson family `blindFamily` and a two-phase hierarchy
`reduced T₀` over it satisfying all four clauses of `Hierarchy.Properties`.
-/

set_option autoImplicit false
noncomputable section

namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The zero vector of grade `0`, viewed as a tag. -/
def zeroTag (F : ℕ → Type) [∀ d, Zero (F d)] : Σ d, F d := ⟨0, 0⟩

open Classical in
/-- `1` if every entry of the word is the zero tag (in particular on the empty word), else `0`. -/
def allZero {F : ℕ → Type} [∀ d, Zero (F d)] {ι : Type} (w : ι → Σ d, F d) : ℂ :=
  if ∀ i, w i = zeroTag F then 1 else 0

open Classical in
/-- A Wilson family whose insertions ignore the gauge field: the insertion of a token is `1`
for the zero tag and `0` otherwise, at every spacing, volume, site and configuration. -/
def blindFamily {g : GaugeGroup} (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (F : ℕ → Type) [∀ d, Zero (F d)] : WilsonFamily g where
  period p := ⟨p + 1, Nat.succ_pos p⟩
  denominator N := ⟨N + 2, by omega⟩
  periodStrict a b hab := by show a + 1 < b + 1; omega
  denominatorStrict a b hab := by show a + 2 < b + 2; omega
  beta N _ := Real.log ((N + 2 : ℕ) : ℝ)
  haar := μ
  probability := inferInstance
  invariantHaar := hH
  Token := Σ d, F d
  insertion _ _ v _ _ := if v = zeroTag F then 1 else 0

/-- The selected phase of `T₀` gives correlation `0` to any word containing the zero tag
(true for any model whose correlations are linear in each field vector). -/
def ZeroInvisible {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀) : Prop :=
  ∀ (n : ℕ) (w : Fin n → T₀.Tag) (x : Points n), (∃ i, w i = zeroTag T₀.Field) →
    T₀.correlation (some T₀.selected) w x = 0

/-- Two phases, realized as the subset `{0, 1}` of `ℝ` (Mathlib has no metric on `Fin 2`). -/
abbrev Phase : Type := ↥({0, 1} : Set ℝ)

/-- The phase that will be selected. -/
def phase0 : Phase := ⟨0, by simp⟩

/-- The other phase. -/
def phase1 : Phase := ⟨1, by simp⟩

/-- The uniform probability measure on the two phases. -/
def phaseMeasure : Measure Phase := (2⁻¹ : ℝ≥0∞) • (Measure.dirac phase0 + Measure.dirac phase1)

variable {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)

open Classical in
/-- Phase correlations of the reduced hierarchy: the selected phase `phase0` is `T₀`'s
selected phase `S`, the unselected (Wilson) correlation is `allZero`, and the other phase
is `2 · allZero − S`, so that the average of the two phases is `allZero`. -/
def redCorrelation {n : ℕ} : Option Phase → (Fin n → T₀.Tag) → Points n → ℂ
  | none, w, _ => allZero w
  | some i, w, x =>
      if i = phase0 then T₀.correlation (some T₀.selected) w x
      else 2 * allZero w - T₀.correlation (some T₀.selected) w x

/-- Actors of the reduced channels: `T₀`'s actors, plus the zero vector for the new channel. -/
def redActor (j : ℕ) : Option (T₀.Channel j) → T₀.Field j
  | none => 0
  | some i => T₀.actor j i

open Classical in
/-- OPE coefficients: `T₀`'s coefficients (set to `0` on channels whose actor is the zero
tag), plus the new channel `none`, whose actor is the zero tag and whose coefficient is
`allZero a` in grade `0` (and `0` in other grades). -/
def redCoefficient {I : Type} [Fintype I] (a : I → T₀.Tag) (j : ℕ) :
    Option (T₀.Channel j) → (I → Spacetime) → Spacetime → ℂ
  | none, _, _ => if j = 0 then allZero a else 0
  | some i, x, o => if (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field then 0
      else T₀.coefficient a j i x o

/-- The reduced hierarchy over the gauge-blind family. -/
def reduced (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure) :
    Hierarchy (blindFamily μ hH T₀.Field) where
  H := T₀.H
  labels := T₀.labels
  theory := T₀.theory
  Field := T₀.Field
  toLabel := T₀.toLabel
  project := id
  Character := Phase
  phaseMeasure := phaseMeasure
  selected := phase0
  correlation := redCorrelation T₀
  continuation := T₀.continuation
  Channel j := Option (T₀.Channel j)
  actor := redActor T₀
  coefficient a j := redCoefficient T₀ a j
  centeredTrace := T₀.centeredTrace

end YMAudit
