import YM.Gauge.Colors
import YM.Space.Orthogonal
import YM.Analysis.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Radial variables

Work with real Lie algebra in physical color coordinates and
symmetric homogeneous (Taylor **coefficients**, not derivative values). The radial constraint is imposed on polynomial potentials at all real positions. No quotient by YM equations in these variables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Labels
open Set WithLp
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

/-- `j` denotes weight `j+2`, polynomial position degree `j+1`, slot degree one. -/
abbrev Raw (G : Gauge) (j : ℕ) := Axis → Tensor.T E4 G.Color (j+1)

/-- Taylor coefficient constrained by radial gauge. -/
def radial (G : Gauge) (j : ℕ) : Submodule ℝ (Raw G j) where
  carrier := {A | (∀ i : Axis, Tensor.Sym (A i)) ∧ ∀ z : E4, ∑ i : Axis, z i • Tensor.diagonal (A i) z = 0}
  zero_mem' := by simp [Tensor.Sym,Tensor.diagonal]
  add_mem' := by
    rintro x y ⟨H,H'⟩ ⟨K,K'⟩
    refine ⟨fun i s r ↦ ?_,fun z ↦ ?_⟩
    · simp [H i s r, K i s r]
    simp only [Tensor.diagonal] at H' K' ⊢
    simp [smul_add, Finset.sum_add_distrib, H', K']
  smul_mem' := by
    rintro c y ⟨H,H'⟩
    refine ⟨fun i s r ↦ ?_,fun z ↦ ?_⟩
    · simp [H i s r]
    simp only [Tensor.diagonal] at H' ⊢
    simp_rw [Pi.smul_apply, smul_apply, smul_comm _ c, ← Finset.smul_sum,
      H', smul_zero]

abbrev Taylor (G : Gauge) (j : ℕ) := ↥(radial G j)

namespace Taylor
variable {G : Gauge} {j : ℕ}

def value (A : Taylor G j) (i : Axis) (z : E4) : G.Color := Tensor.diagonal (A.val i) z

theorem radial_value (A : Taylor G j) (x : E4) : ∑ i, x i • A.value i x = 0 := A.property.2 _

theorem value_ext (A B : Taylor G j) (h : value A = value B) : A = B :=
  Subtype.ext (funext fun i => Tensor.ext_diag _ _ (A.property.1 i) (B.property.1 i) (congr_fun h i))

theorem value_hom (A : Taylor G j) (i : Axis) (x : E4) (t : ℝ) :
    A.value i (t • x) = (t^(j+1)) • A.value i x := by
  have hi := (A.val i).map_smul_univ (fun _ => t) (fun _ => x)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hi; exact hi

def paint (u : G.El) : Taylor G j →ₗ[ℝ] Taylor G j where
  toFun A := ⟨fun i => (G.adjoint u).toContinuousLinearMap.compContinuousMultilinearMap (A.val i), by
    refine ⟨fun i s r ↦ ?_,fun z ↦ ?_⟩
    · exact congr_arg (G.adjoint u) (A.property.1 i s r)
    change ∑ i : Axis, z i • G.adjoint u (value A i z) = _
    rw [← map_zero (G.adjoint u), ← A.radial_value z, map_sum]
    simp only [map_smul] ⟩
  map_add' := by intro x y; apply Subtype.ext; funext i; ext1; exact map_add (G.adjoint u) _ _
  map_smul' := by intro c x; apply Subtype.ext; funext i; ext1; exact map_smul (G.adjoint u) _ _

@[simp] theorem paint_value (u : G.El) (A : Taylor G j) (i x) :
    value (paint u A) i x = G.adjoint u (value A i x) := rfl

def turn (g : Ortho) : Taylor G j →ₗ[ℝ] Taylor G j where
  toFun A := ⟨ fun i => ∑ k, g.val i k •
    ((A.val k).compContinuousLinearMap fun _ ↦ (Ortho.motion g⁻¹).toContinuousLinearMap), by
    constructor
    · intro i x s
      have hX := A.property.1
      simp only [sum_apply, smul_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      apply Finset.sum_congr rfl
      intro k _
      exact congr_arg (fun z : G.Color => g.val i k • z) (hX k (fun i => (Ortho.motion g⁻¹) (x i)) s)
    intro z
    have ht (k : Axis) : ∑ i, z i * g.val i k = Ortho.move g⁻¹ z k := by
      simp only [Ortho.move, M4.at_coord]
      apply Finset.sum_congr rfl; intro i _
      change z i * g.val i k = star (g.val i k) * z i
      rw [star_trivial, mul_comm]
    simp only [Tensor.diagonal, sum_apply, smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ht]
    exact A.radial_value _ ⟩
  map_add' := by
    intro x y; apply Subtype.ext; funext i; ext1 v
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' := by
    intro c x; apply Subtype.ext; funext i; ext1 v
    simp [Finset.smul_sum, smul_comm c]

theorem turn_value (s : Ortho) (A : Taylor G j) (i : Axis) (x : E4) :
    value (turn s A) i x = ∑ k, s.val i k • value A k (Ortho.move s⁻¹ x) := by
  unfold turn value Tensor.diagonal
  simp [Ortho.motion]

@[simp] theorem oneTurn (A : Taylor G j) : turn 1 A = A := by
  apply value_ext; funext i x; rw [turn_value, inv_one, Ortho.move_one]
  change ∑ k : Axis, (1 : M4) i k • _ = _; simp [Matrix.one_apply]

theorem turn_mul (s t : Ortho) (A : Taylor G j) :
    turn (s*t) A = turn s (turn t A) := by
  apply value_ext; funext i x
  simp_rw [turn_value, mul_inv_rev, Ortho.move_mul, Finset.smul_sum, smul_smul]
  change ∑ k, (s.val * t.val) i k • _ = _
  rw [Finset.sum_comm]; simp_rw [Matrix.mul_apply, Finset.sum_smul]

theorem turn_paint (s : Ortho) (u : G.El) (A : Taylor G j) :
    paint u (turn s A) = turn s (paint u A) := by
  apply value_ext; funext i x; simp [turn_value]
end Taylor
end YM.Labels
