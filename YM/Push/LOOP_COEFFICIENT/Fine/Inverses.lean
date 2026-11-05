import Mathlib.Analysis.Complex.Schwarz
import YM.Push.LOOP_COEFFICIENT.Fine.Laplacian


/-!
# Transporting a square fiber gap on a relative-radius ball
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Fine
open Matrix Function Filter Set Lattice Laurent RG Precision Exterior Bloch Wilson Complex Metric
open scoped Topology Matrix.Norms.L2Operator ContDiff BigOperators
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {a : Type} [Fintype a] [DecidableEq a] {M N : Matrix a a ℂ} {e d : ℝ}

def Gap (M : Matrix a a ℂ) (e : ℝ) := ∀ x : EuclideanSpace ℂ a, e*‖x‖ ≤ ‖toEuclideanLin M x‖
omit [DecidableEq a] in
lemma cash_norm (x : EuclideanSpace ℂ a) : cash (WithLp.ofLp x) = ‖x‖^2 := by rw [cash,dotProduct_comm,← EuclideanSpace.inner_eq_star_dotProduct x]; exact inner_self_eq_norm_sq (𝕜:=ℂ) x

lemma Gap.mono (h : Gap M e) (h' : d≤e) : Gap M d := fun x => (mul_le_mul_of_nonneg_right h' (norm_nonneg _)).trans (h x)
lemma Gap.unit (h : Gap M e) (he : 0<e) : IsUnit M := by
  apply Matrix.mulVec_injective_iff_isUnit.mp; intro x y hh
  have hv := h (WithLp.toLp 2 (x-y)); rw [toLpLin_apply, WithLp.ofLp_toLp,Matrix.mulVec_sub,hh, sub_self,WithLp.toLp_zero,norm_zero] at hv
  simpa [sub_eq_zero] using (le_of_mul_le_mul_of_pos_left (hv.trans_eq (mul_zero e).symm) he)









end YM.Push.Loops.Fine
