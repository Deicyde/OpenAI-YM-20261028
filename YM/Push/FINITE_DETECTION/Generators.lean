import Mathlib.Analysis.Calculus.TaylorIntegral
import YM.Next.EXTRACTION.Tails
import YM.Work.B04

/-!
# Bigraded free equation symbols for the `Matches` port

The intended index space there (radial off-shell ideal) can indeed be
presented through homogeneous terms `coefficient * divergence leg`, before
replicating/color averaging any Wilson lifts. This proves the formal-polynomial
assertion behind E near 15206–18 and `WEideal`. Linear curvature `dA` in
these equations (not a substitution of a nonlinear YM equation for a free
one). `z` is a direction in a homogeneous Taylor form; divergence is computed
on that curl homogeneous term. The span is taken on unrestricted coefficient
polynomials and tested for membership of the invariant labels — no assertion
that each *product summand* is invariant, nor that some particular stencil
lift has the desired leading or normalized readout at cutoff!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Generators
open Function Set Filter Maxwell Tensor Labels Analysis MvPolynomial
open scoped BigOperators
variable {G : Gauge} {d : ℕ}



def divMap (j : ℕ) (b : Axis) (z : E4) : Taylor G j →ₗ[ℝ] G.Color :=
  let D : formSpace j G.Color →ₗ[ℝ] G.Color := {
    toFun A := ∑ i : Axis, grad i (Tensor.diagonal (A.val i b)) z
    map_add' A B := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
      change fderiv ℝ (Tensor.diagonal (A.val i b) + Tensor.diagonal (B.val i b)) z _ = _
      rw [fderiv_add ((diag_smooth _ 1).differentiable (by norm_num) _) ((diag_smooth _ 1).differentiable (by norm_num) _)]; rfl
    map_smul' c A := by
      rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      change fderiv ℝ (c • Tensor.diagonal (A.val i b)) z _ = _
      rw [fderiv_const_smul ((diag_smooth _ 1).differentiable (by norm_num) _)]; rfl }
  D.comp potential.toLinearMap









variable {j : ℕ}
def leg (l : Taylor G j →ₗ[ℝ] ℝ) : Pol G := ∑ i : Fin (Labels.dim G j), MvPolynomial.C ((l (axes G j i) : ℝ) : ℂ) * MvPolynomial.X ⟨j,i⟩
lemma leg_at (l : Taylor G j →ₗ[ℝ] ℝ) (A : Jet G) : read A (leg l) = (l (A j) : ℝ) := by
  conv_rhs => rw [← (axes G j).sum_repr (A j),map_sum]
  simp only [leg,Labels.read,map_sum,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,map_smul,smul_eq_mul,
    Complex.ofReal_sum,Complex.ofReal_mul,Labels.coord]
  exact Finset.sum_congr rfl fun _ _ => mul_comm ..


























end YM.Push.FiniteDetection.Generators
