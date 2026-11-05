import YM.Push.LOOP_COEFFICIENT.Frame.Positions

/-!
# Local-to-volume row and quadratic compiler
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Set Filter Matrix Lattice Laurent RG Bloch Complex Block
open scoped Topology ContDiff BigOperators
variable {a b c d z J E F : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] [Fintype J] [DecidableEq J] [Fintype E] [Fintype F]
  {n : Side} {T : Grid n J d} {B : Grid n E a} {D : Site n → Matrix c J ℝ} {M : Momentum → Matrix c d ℂ}

variable (D) in
def shiftMatrix : Matrix (Co n c) J ℝ := of fun i => D i.1 i.2

def native (n : Side) (a : Type) : Grid n (Co n a) a := Equiv.refl _
omit [Fintype c] [DecidableEq c] [DecidableEq J] in
lemma shift_apply (D : Site n → Matrix c J ℝ) (u v x) : (shiftMatrix D *ᵥ v) (x,u) = (D x *ᵥ v) u := rfl


variable [Fintype z] [DecidableEq z]
open scoped Matrix.Norms.Frobenius
variable {C : Grid n F z} {N : Site n → Matrix b F ℝ} {P : Momentum → Matrix b z ℂ}

def rolling (B : Grid n E a) (N : Site n → Matrix b F ℝ) (D : Site n → Matrix c J ℝ) (f : (c → ℝ) → Matrix a b ℝ) (v : J → ℝ) := stack B (native n b) D f v * shiftMatrix N
def row (M : Momentum → Matrix c d ℂ) (P : Momentum → Matrix b z ℂ) (f : (c → ℝ) → Matrix a b ℝ) := (atVertex M f).mul (Vertex.const P)
omit [Fintype a] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq J] [Fintype E] in
lemma rolling_vector (N : Site n → Matrix b F ℝ) (D : Site n → Matrix c J ℝ) (f : (c → ℝ) → Matrix a b ℝ) (v w i) : (rolling B N D f v *ᵥ w) i = (f (D (B i).1 *ᵥ v) *ᵥ N (B i).1 *ᵥ w) (B i).2 := by rw [rolling,← Matrix.mulVec_mulVec,stack_vector]; rfl



def echoed (N : Site n → Matrix b F ℝ) (D : Site n → Matrix c J ℝ) (f : (c → ℝ) → Matrix b b ℝ) (v : J → ℝ) := (shiftMatrix N).transpose * rolling (native n b) N D f v

omit [Fintype c] [DecidableEq b] [DecidableEq c] [DecidableEq J] in
lemma echoed_pair (N : Site n → Matrix b F ℝ) (D : Site n → Matrix c J ℝ) (f : (c → ℝ) → Matrix b b ℝ) (v u w) : u ⬝ᵥ (echoed N D f v *ᵥ w) = ∑ x, (N x *ᵥ u) ⬝ᵥ f (D x *ᵥ v) *ᵥ N x *ᵥ w := by rw [echoed,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]; simp only [dotProduct,Fintype.sum_prod_type, rolling_vector]; rfl

end YM.Push.Loops.Frames
