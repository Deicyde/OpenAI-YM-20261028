import Mathlib.Analysis.PSeries
import YM.Push.LOOP_COEFFICIENT.Block.Magnitude
import YM.Push.LOOP_COEFFICIENT.Block.Portal

/-!
# The aggregate split with its tangent weights
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Matrix Filter Set Lattice Laurent Bloch RG Wilson Complex Portal 
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator
variable {a b d R : Type} [Fintype a] [Fintype b] [Fintype d] [DecidableEq a] [DecidableEq b]

section algebra
variable [CommSemiring R]
def inlet (R a b : Type) [CommSemiring R] [DecidableEq a] [DecidableEq b] : Matrix a (a⊕b) R := of fun i j => if Sum.inl i=j then 1 else 0
def attic (R a b : Type) [CommSemiring R] [DecidableEq a] [DecidableEq b] : Matrix b (a⊕b) R := of fun i j => if Sum.inr i=j then 1 else 0
omit [DecidableEq a] [DecidableEq b] in
lemma direct_mul (M M' : Matrix a a R) (N N' : Matrix b b R) : fromBlocks M 0 0 N * fromBlocks M' 0 0 N' = fromBlocks (M*M') 0 0 (N*N') := by simp [fromBlocks_multiply]
lemma direct_sum (M : Matrix a a R) (N : Matrix b b R) : (inlet R a b).transpose * M * inlet R a b + (attic R a b).transpose * N * attic R a b = fromBlocks M 0 0 N := by
  ext (i|i) (j|j) <;> simp [inlet,attic,Matrix.mul_apply,ite_mul,mul_ite]
lemma inlet_eval (x : a⊕b → R) : inlet R a b *ᵥ x = x ∘ Sum.inl := by ext1; simp [inlet,mulVec,dotProduct,ite_mul]
lemma attic_eval (x : a⊕b → R) : attic R a b *ᵥ x = x ∘ Sum.inr := by ext1; simp [attic,mulVec,dotProduct,ite_mul]


end algebra

variable (P : Portal a) (Q : Portal b) {e η : ℝ}



omit [DecidableEq a] [DecidableEq b] in
lemma direct_eval (M : Matrix a a ℂ) (N : Matrix b b ℂ) (x : CSpace (a⊕b)) : mag (fromBlocks M 0 0 N *ᵥ x)^2 = mag (M *ᵥ (x ∘ Sum.inl))^2 + mag (N *ᵥ (x ∘ Sum.inr))^2 := by rw [← mag_sum,fromBlocks_mulVec]; simp





variable (a b) in
lemma projection_op : ‖inlet ℂ a b‖ ≤ 1 ∧ ‖attic ℂ a b‖ ≤ 1 := ⟨op_of_mag _ zero_le_one (fun x => by rw [inlet_eval,one_mul]; nlinarith [mag_sum x,mag_nonneg x]),op_of_mag _ zero_le_one (fun x => by rw [attic_eval,one_mul]; nlinarith [mag_sum x,mag_nonneg x])⟩

end YM.Push.Loops.Block
