import YM.Push.LOOP_COEFFICIENT.LogKernel

/-!
# Thin-factor calculus for the residue trace

Dual formulation (without using a matrix trace-norm instance). Thinness is
only needed of differences, after cancellation, two-sided normalizations,
including at shifted momenta. Helpers for rectangular low-rank terms and
summably diagonal factors. No trace dividing by residue count.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators
variable {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c]

structure Thin (X : Matrix a b ℂ) (C : ℝ) : Prop where
  pos : 0≤C
  bill (Y : Matrix b a ℂ) : ‖(X*Y).trace‖ ≤ C * ‖Y‖

variable {X Y : Matrix a b ℂ} {C D C' D' : ℝ}
namespace Thin
omit [DecidableEq b] in
lemma mono (h : Thin X C) (he : C≤D) : Thin X D := ⟨h.pos.trans he, fun Y => (h.bill Y).trans (by gcongr)⟩
omit [DecidableEq b] in
lemma zero : Thin (0 : Matrix a b ℂ) 0 := ⟨le_rfl,fun _ => by simp⟩
omit [DecidableEq b] in
lemma add (h : Thin X C) (h' : Thin Y D) : Thin (X+Y) (C+D) := ⟨add_nonneg h.pos h'.pos, fun Z => by rw [Matrix.add_mul,Matrix.trace_add,add_mul]; exact (norm_add_le ..).trans (add_le_add (h.bill Z) (h'.bill Z))⟩
omit [DecidableEq b] in
lemma smul (s : ℂ) (h : Thin X C) : Thin (s • X) (‖s‖*C) := ⟨mul_nonneg (norm_nonneg _) h.pos,fun Z => by rw [Matrix.smul_mul,trace_smul,norm_smul,mul_assoc]; gcongr; exact h.bill Z⟩
omit [DecidableEq b] in
lemma neg (h : Thin X C) : Thin (-X) C := by simpa using h.smul (-1)
omit [DecidableEq b] in
lemma sub (h : Thin X C) (h' : Thin Y D) : Thin (X-Y) (C+D) := by simpa [sub_eq_add_neg] using h.add h'.neg
omit [DecidableEq b] in
lemma left (h : Thin X C) {Z : Matrix b c ℂ} (hz : ‖Z‖ ≤ D) : Thin (X*Z) (C*D) :=
  ⟨mul_nonneg h.pos ((norm_nonneg _).trans hz),fun M => by
    rw [Matrix.mul_assoc,mul_assoc]; exact (h.bill _).trans (mul_le_mul_of_nonneg_left (op_cost hz (le_refl _)) h.pos)⟩
omit [DecidableEq c] in
lemma right {Z : Matrix a b ℂ} {X : Matrix b c ℂ} (h : Thin X C) (hz : ‖Z‖ ≤ D) : Thin (Z*X) (D*C) :=
  ⟨mul_nonneg ((norm_nonneg _).trans hz) h.pos,fun M => by
    rw [Matrix.mul_assoc, ← Matrix.trace_mul_cycle' X M Z, mul_comm D C,mul_assoc, mul_comm D ‖M‖]; exact (h.bill _).trans (mul_le_mul_of_nonneg_left (op_cost (le_refl _) hz) h.pos)⟩
lemma trace {X : Matrix a a ℂ} (h : Thin X C) : ‖X.trace‖ ≤ C := by
  cases isEmpty_or_nonempty a with
  | inl hl => simpa [Matrix.trace] using h.pos
  | inr hr => simpa using h.bill 1


end Thin

structure CoveredPair (X Y : Matrix a b ℂ) (C D : ℝ) : Prop where
  first : ‖X‖≤C
  second : ‖Y‖≤C
  gap : Thin (X-Y) D

namespace CoveredPair

lemma mul {V W : Matrix b c ℂ} (h : CoveredPair X Y C D) (h' : CoveredPair V W C' D') : CoveredPair (X*V) (Y*W) (C*C') (C*D'+D*C') := by
  refine ⟨op_cost h.first h'.first,op_cost h.second h'.second,?_⟩; rw [show X*V-Y*W=X*(V-W)+(X-Y)*W by rw [Matrix.mul_sub, Matrix.sub_mul]; abel]
  exact (h'.gap.right h.first).add (h.gap.left h'.second)
lemma inv {X Y : Matrix a a ℂ} (h : Thin (X-Y) D) (hx : IsUnit X) (hy : IsUnit Y) (h₁ : ‖X⁻¹‖ ≤ C) (h₂ : ‖Y⁻¹‖ ≤ C) :
    CoveredPair X⁻¹ Y⁻¹ C (C*D*C) := by
  refine ⟨h₁,h₂,?_⟩
  rw [show X⁻¹-Y⁻¹ = -(X⁻¹*(X-Y)*Y⁻¹) by rw [mul_sub,sub_mul,Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hx),mul_assoc _ Y,Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hy)]; simp]
  exact ((h.right h₁).left h₂).neg
end CoveredPair
end YM.Push.Loops
