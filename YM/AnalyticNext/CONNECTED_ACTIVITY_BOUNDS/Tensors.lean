import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.PSeries
import YM.Next.SCHEDULE.Blocks

/-!
# Conditional Gaussian price on arcs

No covariance independence heuristic. θ integrated afterwards. Use true marginal law.
Prove for any including empty position sets, with push-volume normalized matches.
This lemma also allows sequential triangular centers for marker conditioning.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Centered.Moment
open Function MeasureTheory Filter Matrix Set
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : n→Prop) [DecidablePred P]

abbrev Backside := {i : n // ¬ P i}
abbrev Twin := Subtype P



def ops (A : Matrix n n ℝ) : Matrix (Twin P) (Twin P) ℝ := A.submatrix (↑) (↑)

def pushUp (v : Twin P→ℝ) (i : n) := if h : P i then v ⟨i,h⟩ else 0

def fulsome (v : n→ℝ) (p : Twin P) := v p

omit [DecidableEq n] in
lemma projection (A : Matrix n n ℝ) (v : Twin P→ℝ) : fulsome P (A *ᵥ pushUp P v)=ops P A *ᵥ v := by
  funext i
  unfold fulsome Matrix.mulVec dotProduct
  rw [← Fintype.sum_subtype_add_sum_subtype P]; simp only
  rw [show (∑ p : Backside P,A i p * pushUp P v p)=0 from Finset.sum_eq_zero fun j _ => by
    rw [pushUp,dif_neg j.property,mul_zero],add_zero]
  exact Finset.sum_congr rfl fun j _ => congr_arg _ (dif_pos j.property)

omit [DecidableEq n] in
lemma hands (v : Twin P→ℝ) (w : n→ℝ) : dotProduct w (pushUp P v)= dotProduct (fulsome P w) v := by
  unfold dotProduct; rw [← Fintype.sum_subtype_add_sum_subtype P]
  rw [show (∑ p : Backside P,w p * pushUp P v p)=0 from Finset.sum_eq_zero fun j _ => by
    rw [pushUp,dif_neg j.property,mul_zero],add_zero]
  exact Finset.sum_congr rfl fun j _ => congr_arg _ (dif_pos j.property)

section stan

variable (A : Matrix n n ℝ) (hp : A.PosDef)







include hp




-- Density and integral. Use numerical ratio first; positivity cancels.







end stan
end YM.AnalyticNext.ConnectedActivity.Centered.Moment
