import YM.Space.Configurations
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Star.Unitary

/-!
Orthogonal transformations, skew generators and the restriction to `H`.
 (later acts on the actual W spaces).
-/

set_option autoImplicit false
noncomputable section
namespace YM

open MeasureTheory Set Filter WithLp
open scoped Matrix.Norms.Frobenius Matrix InnerProductSpace Topology

abbrev M4 := Matrix Axis Axis ℝ
abbrev Ortho := ↥(Matrix.unitaryGroup Axis ℝ)

namespace M4

def move (A : M4) (x : E4) := Matrix.toEuclideanLin A x

theorem at_coord (A : M4) (x : E4) (i : Axis) : move A x i = ∑ j, A i j * x j := rfl

@[simp] theorem move_one (x : E4) : move 1 x = x := by
  apply WithLp.ofLp_injective 2
  change (1 : M4) *ᵥ ofLp x = ofLp x
  rw [Matrix.one_mulVec]

theorem move_mul (A B : M4) (x : E4) : move (A*B) x = move A (move B x) := by
  apply WithLp.ofLp_injective 2
  exact (Matrix.mulVec_mulVec (ofLp x) A B).symm

@[simp] theorem move_basis (A : M4) (i j : Axis) : move A (basis j) i = A i j := by
  simp [at_coord, basis_eq]
end M4

namespace Ortho

@[simp] theorem transp (s : Ortho) : s.val.transpose * s.val = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using (show star s.val * s.val = 1 from s.2.1)

def move (s : Ortho) (x : E4) := M4.move s.val x

theorem move_mul (s r : Ortho) (x : E4) : move (s*r) x = move s (move r x) :=
  M4.move_mul _ _ _

@[simp] theorem move_one (x : E4) : move 1 x = x := M4.move_one x
@[simp] theorem move_inv (s : Ortho) (x : E4) : move s (move s⁻¹ x) = x := by rw [← move_mul]; simp
@[simp] theorem inv_move (s : Ortho) (x : E4) : move s⁻¹ (move s x) = x := by rw [← move_mul]; simp

theorem move_norm (s : Ortho) (x : E4) : ‖move s x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change dotProduct (s.val *ᵥ ofLp x) (s.val *ᵥ ofLp x) = _
  rw [← Matrix.dotProduct_transpose_mulVec s.val (ofLp x) (s.val *ᵥ ofLp x),
    Matrix.mulVec_mulVec, transp, Matrix.one_mulVec]

def motion (s : Ortho) : E4 ≃ₗᵢ[ℝ] E4 where
  toFun := move s
  invFun := move s⁻¹
  map_add' _ _ := (Matrix.toEuclideanLin s.val).map_add _ _
  map_smul' _ _ := (Matrix.toEuclideanLin s.val).map_smul _ _
  left_inv := inv_move _
  right_inv := move_inv _
  norm_map' := move_norm _

@[simp] theorem motion_at (s : Ortho) (x : E4) : motion s x = move s x := rfl

theorem move_injective (s : Ortho) : Function.Injective (move s) := (motion s).injective

@[ext] theorem ext (s r : Ortho) (h : ∀ x, move s x = move r x) : s = r := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  rw [← M4.move_basis s.val i j, ← M4.move_basis r.val i j]
  exact congrArg (fun x : E4 => x i) (h (basis j))
end Ortho

/-! Restriction to signed-permutation group. -/
namespace Signed

def matrix (s : Signed) : M4 := Matrix.of fun b a =>
  if s.perm a = b then (if s.flip a then -1 else 1) else 0

lemma matrix_at (s : Signed) (a b : Axis) :
    s.matrix b a = if s.perm a = b then (if s.flip a then -1 else 1) else 0 := rfl

def ortho (s : Signed) : Ortho := ⟨s.matrix, by
  rw [Matrix.mem_unitaryGroup_iff']
  apply Matrix.ext
  intro i j
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_eq_single_of_mem (s.perm i) (Finset.mem_univ _)]
  · rcases eq_or_ne i j with e | e
    · subst j; rw [matrix_at]; split_ifs <;> simp_all
    · rw [matrix_at, matrix_at]
      simp [e, Ne.symm e]
  · intro b hb h
    rw [matrix_at]
    simp [Ne.symm h]⟩

theorem ortho_move (s : Signed) (x : E4) : Ortho.move s.ortho x = toLp 2 (s.act x.ofLp) := by
  apply PiLp.ext
  intro b
  obtain ⟨a,rfl⟩ := s.perm.surjective b
  rw [Ortho.move, M4.at_coord]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · simp only [ortho, matrix_at, ↓reduceIte, act_at]; split <;> simp
  · intro j _ h; simp [ortho, matrix_at, h]

def inclusionO : Signed →* Ortho where
  toFun := ortho
  map_one' := Ortho.ext _ _ (by simp [ortho_move])
  map_mul' x y := Ortho.ext _ _ (by simp [Ortho.move_mul, ortho_move, act_mul])

def reflect (i : Axis) := ortho (mirror i)

@[simp] theorem mirrored (a i : Axis) (x : E4) :
    Ortho.move (reflect a) x i = if i = a then - x i else x i := by
  simp [reflect, ortho_move, act, mirror, eq_comm]
end Signed

namespace Ortho

/-- `so(4)` as real skew matrices. -/
def skewSpace : Submodule ℝ M4 where
  carrier := {A | star A = - A}
  add_mem' := by
    intro a b ha hb
    change star (a+b) = -(a+b)
    rw [star_add, ha, hb, neg_add]
  smul_mem' := by
    intro t a h
    change star (t • a) = -(t • a)
    rw [star_smul, star_trivial, h, smul_neg]
  zero_mem' := by simp

abbrev Skew := ↥skewSpace

def oneParameter (Ω : Skew) (t : ℝ) : Ortho := ⟨NormedSpace.exp (t • Ω.val), by
  haveI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewSpace.smul_mem _ Ω.property)⟩

/-- Entry `(i,j)=1`, `(j,i)=-1` when distinct. In `Plane timeAxis l`,
coordinate vector field is `xˡ∂_y - y∂_l` with `y = Euclidean time` . -/
def plane (i j : Axis) : Skew := ⟨Matrix.single i j 1 - Matrix.single j i 1, by
  change star _ = -_
  simp [Matrix.star_eq_conjTranspose]⟩
end Ortho

end YM
