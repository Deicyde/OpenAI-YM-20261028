import YM.SectorNext.RECONNECTED_LOCALITY.Gaussian
import YM.SectorNext.RECONNECTED_LOCALITY.Swell


set_option warningAsError false

/-! # True covariance and common Gram

The symmetrized column prescription $C = front(W,A)$ isn't positive by
definition. Prove large-radius receipt explicitly from earlier tracking and
positive-spectrum input plus a single delay (see `brighten`). Also realize true
probability and jointly Borel Gram root for Print/F laws (without asserting even
continuity of the input A!). Do not ever use locality of this root. -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Ice
open Finset Matrix Function Filter MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder Topology

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {g : Radar I} {A : Matrix I I ℝ} {W : I→Finset I} {r δ k σ ν L b : ℝ}



def cold (k δ ν L b : ℝ) := wet δ L k * Real.exp (-ν*b) ≤ δ/k^2/2





omit [DecidableEq I] in
lemma Buoy.hermitian (h : Buoy A r) (hr : 0≤r) (he : A.transpose=A) : A.IsHermitian ∧ A.PosSemidef := by
  have hh : A.IsHermitian := IsHermitian.ext fun i j => by
    rw [star_trivial]; exact congrFun (congrFun he _) _
  refine ⟨hh,posSemidef_iff_dotProduct_mulVec.mpr ⟨hh,fun x => ?_⟩⟩
  rw [star_trivial]; exact (mul_nonneg hr (fuel_nonneg x)).trans (h x)



/-- Useful to purchase a true joint Borel generator. Use the Mathlib C* instances
on reals and ContinuousOn sqrt, not a measurable eigenbasis axiom. -/
def drawn (A : Matrix I I ℝ) : Window.Cov I := A


section measured
variable {T : Type*} [MeasurableSpace T]

local instance : MeasurableSpace (Matrix I I ℝ) := borel _
local instance : BorelSpace (Matrix I I ℝ) := ⟨rfl⟩

omit [DecidableEq I] in
lemma matrix_meas (A : T→Matrix I I ℝ) (h : ∀ i j,Measurable (fun t => A t i j)) :
    Measurable A := by
  let g : (I→I→ℝ) → Matrix I I ℝ := id
  have hg : Continuous g := continuous_matrix fun i j => show Continuous (fun x:I→I→ℝ => x i j) from by fun_prop
  exact hg.measurable.comp (measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => h i j)))

omit [Fintype I] [DecidableEq I] in
lemma entries_meas {A : T→Matrix I I ℝ} (h : Measurable A) (i j : I) :
    Measurable (fun t => A t i j) :=
  (show Continuous (fun x:Matrix I I ℝ => x i j) from by fun_prop).measurable.comp h



-- entrywise inverse meas incl singular case, even if witnesses on nonparametrized slots
lemma det_bonds (A : T→Matrix I I ℝ) (he : ∀ i j,Measurable (fun t => A t i j)) :
    Measurable (fun t => (A t).det) := by
  simp_rw [det_apply']
  fun_prop (disch:=aesop)

lemma inv_bonds (A : T→Matrix I I ℝ) (he : ∀ i j,Measurable (fun t => A t i j)) (i j : I) :
    Measurable (fun t => (A t)⁻¹ i j) := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,adjugate_apply]
  apply Measurable.mul (det_bonds A he).inv; apply det_bonds; intro a d
  by_cases hh : a=j
  · subst a; simp only [updateRow_self]; fun_prop
  simp_rw [updateRow_ne hh]; exact he a d

omit [Fintype I] in
lemma floe_meas (A : T→ Matrix I I ℝ) (h : ∀ i j,Measurable (fun t=> A t i j)) (W : I→Finset I) (u : T→ℝ) (hu : Measurable u) (i j : I) :
    Measurable (fun t=> floe W (A t) (u t) i j) := by
  by_cases he : j∈W j
  · by_cases ha : i∈W j
    · simp_rw [floe,of_apply,dif_pos he,dif_pos ha]
      apply inv_bonds (I:=↥(W j))
      intro a d; dsimp only [hotel,face,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,submatrix_apply]
      exact (h _ _).add (hu.mul_const _)
    simp_rw [floe_else ha]; exact measurable_const
  simp_rw [floe,of_apply,dif_neg he]; exact measurable_const

omit [Fintype I] in
lemma front_meas (A : T→ Matrix I I ℝ) (h : ∀ i j,Measurable (fun t=> A t i j)) (W : I→Finset I) (i j : I) :
    Measurable (fun t=> front W (A t) i j) := by
  simp_rw [front,Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,transpose_apply]
  exact ((floe_meas A h W _ measurable_const i j).add (floe_meas A h W _ measurable_const j i)).const_mul _
end measured


end YM.SectorNext.Reconnect.Ice
