import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Compact matrix gauge groups
The gauge input is the closed matrix image in its given unitary representation. Matrix estimates use the Frobenius norm and the group carries probability Haar measure.
-/

set_option autoImplicit false
noncomputable section
namespace YM

open MeasureTheory
open scoped Matrix.Norms.Frobenius Topology

/-- We index a representation of dimension `n+1`. -/
abbrev GaugeU (n : ℕ) := Matrix.unitaryGroup (Fin (n+1)) ℂ

/-- A closed compact matrix group in its fixed faithful unitary representation. -/
structure Gauge where
  n : ℕ
  imageGroup : Subgroup (GaugeU n)
  closed_imageGroup : IsClosed (imageGroup : Set (GaugeU n))

namespace Gauge

section Norms
variable {r : ℕ}

/-- Trace characterization of the Frobenius norm. -/
theorem frob_sq (A : Matrix (Fin r) (Fin r) ℂ) :
    ‖A‖ ^ 2 = (A * star A).trace.re := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  swap
  · simp_rw [Real.rpow_two]
    exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  simp_rw [Real.rpow_two, Matrix.trace, Complex.re_sum, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem mul_frob_eq (A B : Matrix (Fin r) (Fin r) ℂ) (h : star A * A = 1) :
    ‖A * B‖ = ‖B‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), frob_sq, frob_sq, star_mul,
    Matrix.trace_mul_cycle, mul_assoc _ (star A) A, h, mul_one, Matrix.trace_mul_comm]

theorem frob_mul_eq (A B : Matrix (Fin r) (Fin r) ℂ) (h : B * star B = 1) :
    ‖A * B‖ = ‖A‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), frob_sq, frob_sq]
  simp only [star_mul, _root_.mul_assoc, ← _root_.mul_assoc B, h, one_mul]

theorem unitary_frob {A : Matrix (Fin r) (Fin r) ℂ} (h : A * star A = 1) :
    ‖A‖ = Real.sqrt (r : ℝ) := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), frob_sq, h,
    Matrix.trace_one, Fintype.card_fin, Complex.natCast_re]
  rw [Real.sq_sqrt]; positivity

theorem compactGaugeU (n : ℕ) : CompactSpace (GaugeU n) := by
  refine isCompact_iff_compactSpace.mp ?_
  letI : ProperSpace (Matrix (Fin (n+1)) (Fin (n+1)) ℂ) := FiniteDimensional.proper ℝ _
  exact (isCompact_closedBall 0 (Real.sqrt ((n+1 : ℕ) : ℝ))).of_isClosed_subset
    isClosed_unitary fun A h ↦ by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq (unitary_frob (Matrix.mem_unitaryGroup_iff.mp h))
end Norms

variable (G : Gauge)

/-- Dimension of the defining representation (not number of Lie colors). -/
abbrev repDim := G.n + 1

theorem dimPos : 0 < G.repDim := Nat.succ_pos _

/-- Physical link state space. -/
abbrev El := ↥G.imageGroup

instance : CompactSpace G.El := by
  letI := compactGaugeU G.n
  exact isCompact_iff_compactSpace.mp G.closed_imageGroup.isCompact

instance : SecondCountableTopology G.El := by
  haveI : SecondCountableTopology (Matrix (Fin (G.n+1)) (Fin (G.n+1)) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin (G.n+1) → Fin (G.n+1) → ℂ))
  haveI : SecondCountableTopology (GaugeU G.n) :=
    inferInstanceAs
      (SecondCountableTopology ↥((GaugeU G.n : Set (Matrix (Fin (G.n+1)) (Fin (G.n+1)) ℂ))))
  exact inferInstanceAs (SecondCountableTopology ↥(G.imageGroup : Set (GaugeU G.n)))

abbrev Mat := Matrix (Fin G.repDim) (Fin G.repDim) ℂ

def mat (u : G.El) : G.Mat := (u.val).val

@[fun_prop] theorem continuous_mat : Continuous G.mat :=
  continuous_subtype_val.comp continuous_subtype_val

theorem mat_injective : Function.Injective G.mat := fun _ _ h ↦
  Subtype.ext (Subtype.ext h)

theorem closed_matrices : IsClosed (Set.range G.mat) :=
  (isCompact_range G.continuous_mat).isClosed

@[simp] theorem mat_one : G.mat 1 = 1 := rfl
@[simp] theorem mat_mul (u v : G.El) : G.mat (u*v) = G.mat u * G.mat v := rfl
@[simp] theorem mat_inv (u : G.El) : G.mat u⁻¹ = star (G.mat u) := rfl
@[simp] theorem mat_mul_star (u : G.El) : G.mat u * star (G.mat u) = 1 := u.val.property.2
@[simp] theorem mat_star_mul (u : G.El) : star (G.mat u) * G.mat u = 1 := u.val.property.1

/-- `s(U)`. -/
def price (u : G.El) : ℝ := 1 - (G.mat u).trace.re / G.repDim

/-- The normalized HS chord, not the operator norm. -/
def chord (u : G.El) : ℝ := ‖G.mat u - 1‖ / Real.sqrt G.repDim

theorem chord_price (u : G.El) : G.chord u ^ 2 = 2 * G.price u := by
  unfold chord price
  rw [div_pow, frob_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [star_sub, star_one, mul_sub, sub_mul, one_mul, mul_one,
    mat_mul_star]
  simp only [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin,
    Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def,
    Complex.sub_re, Complex.conj_re, Complex.natCast_re]
  field_simp
  ring

@[simp] theorem chord_one : G.chord 1 = 0 := by simp [chord]
@[simp] theorem price_one : G.price 1 = 0 := by
  have := G.chord_price 1; simpa using this.symm

theorem chord_nonneg (u : G.El) : 0 ≤ G.chord u := by unfold chord; positivity

theorem chord_le_two (u : G.El) : G.chord u ≤ 2 := by
  unfold chord
  rw [div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast G.dimPos))]
  apply (norm_sub_le _ _).trans
  rw [unitary_frob (G.mat_mul_star u), unitary_frob (show (1 : Matrix (Fin G.repDim) (Fin G.repDim) ℂ) * star 1 = 1 from G.mat_mul_star 1)]
  rw [two_mul]

theorem price_range (u : G.El) : G.price u ∈ Set.Icc (0 : ℝ) 2 := by
  have h := G.chord_price u
  have h1 := G.chord_le_two u
  constructor <;> nlinarith [G.chord_nonneg u]

theorem chord_triangle (u v : G.El) : G.chord (u*v) ≤ G.chord u + G.chord v := by
  have h :‖G.mat u * G.mat v - 1‖ ≤ ‖G.mat u - 1‖ + ‖G.mat v - 1‖ := calc
    ‖G.mat u * G.mat v - 1‖ = ‖(G.mat u - 1) + G.mat u * (G.mat v - 1)‖ := by
      simp only [mul_sub, mul_one]; congr 1; abel
    _ ≤ _ := by
      simpa only [mul_frob_eq _ _ (mat_star_mul G u)] using
        norm_add_le (G.mat u - 1) (G.mat u * (G.mat v - 1))
  unfold chord
  rw [G.mat_mul, ← add_div]
  exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)

@[simp] theorem price_inv (u : G.El) : G.price u⁻¹ = G.price u := by
  simp [price, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]

@[simp] theorem price_conj (u v : G.El) : G.price (u*v*u⁻¹) = G.price v := by
  have h : (G.mat (u*v*u⁻¹)).trace = (G.mat v).trace := by
    simp only [G.mat_mul, G.mat_inv, Matrix.trace_mul_cycle, G.mat_star_mul, one_mul]
  unfold price
  rw [h]

@[simp] theorem chord_inv (u : G.El) : G.chord u⁻¹ = G.chord u := by
  rw [← sq_eq_sq₀ (chord_nonneg _ _) (chord_nonneg _ _), chord_price, price_inv, chord_price]

@[simp] theorem chord_conj (u v : G.El) : G.chord (u*v*u⁻¹) = G.chord v := by
  rw [← sq_eq_sq₀ (chord_nonneg _ _) (chord_nonneg _ _), chord_price, price_conj, chord_price]

@[fun_prop] theorem continuous_chord : Continuous G.chord := by unfold chord; fun_prop
@[fun_prop] theorem continuous_price : Continuous G.price := by
  have h : G.price = fun x ↦ G.chord x ^ 2 / 2 := by
    funext; rw [G.chord_price]; ring
  rw [h]; fun_prop

/-! Choose Borel on this subtype. Do not also introduce a measurable-space
instance on `GaugeU`. -/
instance elMeasurableSpace : MeasurableSpace G.El := borel _
instance elBorelSpace : BorelSpace G.El := ⟨rfl⟩

def allElements : TopologicalSpace.PositiveCompacts G.El :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Probability Haar used throughout including blocked expectations. -/
def probHaar : Measure G.El := Measure.haarMeasure G.allElements

instance probHaar_isHaar : G.probHaar.IsHaarMeasure := by unfold probHaar; infer_instance
instance probHaar_isProbability : IsProbabilityMeasure G.probHaar where
  measure_univ := @Measure.haarMeasure_self G.El _ _ _ _ _ G.allElements

instance probHaar_rightInv : G.probHaar.IsMulRightInvariant := by
  constructor
  intro u
  apply Eq.symm
  refine (Measure.haarMeasure_eq_iff G.allElements _).2 ?_
  change (Measure.map _ G.probHaar) Set.univ = 1
  rw [Measure.map_apply (measurable_mul_const u) MeasurableSet.univ]
  simp

instance probHaar_invInv : G.probHaar.IsInvInvariant := by
  constructor
  apply Eq.symm
  refine (Measure.haarMeasure_eq_iff G.allElements _).2 ?_
  change (Measure.map Inv.inv G.probHaar) Set.univ = 1
  rw [Measure.map_apply measurable_inv MeasurableSet.univ]; simp

theorem preserve_inv : MeasurePreserving (Inv.inv : G.El → G.El) G.probHaar G.probHaar :=
  Measure.measurePreserving_inv _

theorem preserve_two_sided (u v : G.El) :
    MeasurePreserving (fun x : G.El => u*x*v) G.probHaar G.probHaar :=
  (measurePreserving_mul_right G.probHaar v).comp (measurePreserving_mul_left G.probHaar u)

end Gauge
end YM
