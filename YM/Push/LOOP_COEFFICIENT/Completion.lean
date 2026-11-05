import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.Pressure.Seeds

/-!
# Full gauge completion and determinants in real physical coordinates

 splitting argument, the algebra *assuming the tangent identities*. No
omission of gauge slots (even harmonic). `R` sends gauge increments to joint
increments and `T` the raw slice increments to joint ones; their juxtaposition
conjugates the action Hessian `Q` to a block with only the slice `H`. Not an
off-shell assertion. `L` is an arbitrary rectangular gauge square.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function

variable {m n k l : Type*}

def sides (A : Matrix m n ℝ) (B : Matrix m k ℝ) : Matrix m (n ⊕ k) ℝ :=
  of fun i j => j.elim (A i) (B i)

@[simp] lemma sides_left (A : Matrix m n ℝ) (B : Matrix m k ℝ) i j : sides A B i (.inl j) = A i j := rfl
@[simp] lemma sides_right (A : Matrix m n ℝ) (B : Matrix m k ℝ) i j : sides A B i (.inr j) = B i j := rfl

variable [Fintype m] [Fintype n] [Fintype k] [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq k]

omit [Fintype n] [Fintype k] [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq k] in
lemma mul_sides (L : Matrix l m ℝ) (A : Matrix m n ℝ) (B : Matrix m k ℝ) :
    L * sides A B = sides (L * A) (L * B) := by
  ext i j; cases j <;> rfl

omit [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k] in
lemma sides_pair (A A' : Matrix m n ℝ) (B B' : Matrix m k ℝ) :
    (sides A B).transpose * (sides A' B') =
      fromBlocks (A.transpose * A') (A.transpose * B') (B.transpose * A') (B.transpose * B') := by
  ext i j; cases i <;> cases j <;> rfl

lemma blockComplete (A : Matrix n n ℝ) (B : Matrix n k ℝ) (H : Matrix k k ℝ) :
    (fromBlocks (0 : Matrix n n ℝ) 0 0 H + (sides A B).transpose * sides A B).det =
      A.det^2 * H.det := by
  let D := fromBlocks A B 0 (1 : Matrix k k ℝ)
  rw [show fromBlocks (0 : Matrix n n ℝ) 0 0 H + (sides A B).transpose * sides A B =
        D.transpose * fromBlocks (1 : Matrix n n ℝ) 0 0 H * D by
      simp [D, sides_pair, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_add, add_comm]]
  simp only [D, det_mul, det_transpose, det_fromBlocks_zero₂₁, det_one]; ring

/-- Determinant squaring; reindex the joint coordinates in any declared order. -/
lemma complete_det (Q : Matrix m m ℝ) (R : Matrix m n ℝ) (T : Matrix m k ℝ)
    (H : Matrix k k ℝ) (L : Matrix n m ℝ) (e : (n ⊕ k) ≃ m)
    (h : (sides R T).transpose * Q * sides R T = fromBlocks 0 0 0 H) :
    (Q + L.transpose * L).det * ((sides R T).submatrix e id).det^2 = (L * R).det^2 * H.det := by
  let D := (sides R T).submatrix e id
  have he (X : Matrix m m ℝ) : D.transpose * (X.submatrix e e) * D =
      (sides R T).transpose * X * sides R T := by
    dsimp only [D]
    rw [transpose_submatrix, submatrix_mul_equiv _ _ _ e, submatrix_mul_equiv _ _ _ e,
      submatrix_id_id]
  have hh : (sides R T).transpose * (Q + L.transpose * L) * sides R T =
        fromBlocks 0 0 0 H + (sides (L * R) (L * T)).transpose * sides (L * R) (L * T) := by
    rw [Matrix.mul_add, Matrix.add_mul, h, ← mul_sides, transpose_mul]
    simp only [Matrix.mul_assoc]
  change _ * D.det^2 = _
  rw [← blockComplete (L * R) (L * T) H, ← hh, ← he, det_mul, det_mul, det_transpose,
    det_submatrix_equiv_self]
  ring

end YM.Push.Loops
