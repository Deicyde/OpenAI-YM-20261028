import Mathlib.Analysis.PSeries
import YM.Push.LOOP_COEFFICIENT.Block.Basis
import YM.Push.LOOP_COEFFICIENT.Block.Induce

/-!
# Internal pair identification needed only at flat
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Matrix Function Set Filter Lattice Laurent RG Bloch Wilson Complex Portal
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {L : Side} {a b c d e : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype e] [DecidableEq a] [DecidableEq b] [DecidableEq c] {S : Set Momentum}
def Rep (S : Set Momentum) (U : Vertex e (Co L a) (Co L b)) (V : Vertex d a b) := ∀ q∈S,∀ l : Site L, U.base q * place b q l = place a q l * V.base (aliasAt q l)
namespace Rep
variable {U U' : Vertex e (Co L a) (Co L b)} {V V' : Vertex d a b}
lemma induce (Y : Profiles L d e) (V : Vertex d a b) : Rep S (induce V Y) V := fun q _ l => by
  simp only [Block.induce,channel,LinearMap.comp_apply,LinearMap.flip_apply,matrixMulLinear,LinearMap.mk₂_apply,Matrix.sum_mul]
  rw [Fintype.sum_eq_single l (fun j hj => ?_), Matrix.mul_assoc _ (select b q l),basis_pair,if_pos rfl,Matrix.mul_one]
  rw [Matrix.mul_assoc _ (select b q j),basis_pair,if_neg hj, Matrix.mul_zero]
omit [Fintype e] in
lemma realize (h : Rep S U V) {q} (hq : q∈S) : U.base q = ∑ l : Site L, channel q q l l (V.base (aliasAt q l)) := by rw [← Matrix.mul_one (U.base q), ← place_select (L:=L) q, Matrix.mul_sum]; exact Finset.sum_congr rfl fun l _ => by rw [← Matrix.mul_assoc,h q hq]; rfl

omit [Fintype e] in lemma add (h : Rep S U V) (h' : Rep S U' V') : Rep S (U.add U') (V.add V') := fun q hq l => by simp only [Vertex.add,Pi.add_apply, Matrix.add_mul,Matrix.mul_add,h q hq,h' q hq]
omit [Fintype e] in lemma smul (h : Rep S U V) (z : ℂ) : Rep S (U.smul z) (V.smul z) := fun q hq l => by simp only [Vertex.smul,Pi.smul_apply, Matrix.smul_mul,Matrix.mul_smul,h q hq]
omit [Fintype e] in lemma zero : Rep S (Vertex.const (d:=e) (a:=Co L a) (b:=Co L b) 0) (Vertex.const (d:=d) 0) := by intro q hq l; simp [Vertex.const]
omit [Fintype e] in lemma id : Rep S (Vertex.id (d:=e) (a:=Co L a)) (Vertex.id (d:=d)) := by intro q hq l; simp [Vertex.id,Vertex.const]
omit [Fintype e] in
lemma mul {U' : Vertex e (Co L b) (Co L c)} {V'} (h : Rep S U V) (h' : Rep S U' V') : Rep S (U.mul U') (V.mul V') := by intro q hq l; dsimp only [Vertex.mul]; rw [Matrix.mul_assoc,h' q hq,← Matrix.mul_assoc,h q hq,Matrix.mul_assoc]
omit [Fintype e] in lemma pow {U : Vertex e (Co L a) (Co L a)} {V : Vertex d a a} (h : Rep S U V) (k : ℕ) : Rep S (U.pow k) (V.pow k) := by induction k with
  | zero => exact Rep.id
  | succ _ ih => exact ih.mul h
omit [Fintype e] in lemma roll {U : Vertex e (Co L a) (Co L a)} {V : Vertex d a a} (h : Rep S U V) : Rep S U.roll V.roll := by
  apply Rep.id.add; generalize depth=k; induction k with
  | zero => exact Rep.zero
  | succ k ih => exact ih.add (h.pow _)
omit [Fintype e] in lemma unit {U : Vertex e (Co L a) (Co L a)} {V : Vertex d a a} (h : Rep S U V) {q} (hq : q∈S) (hu : ∀ i : Site L, IsUnit (V.base (aliasAt q i))) : IsUnit (U.base q) := by
  let M := ∑ l,place a q l * (V.base (aliasAt q (L:=L) l))⁻¹ * select a q l
  have he : U.base q * M = 1 := by
    rw [show (1:Matrix (Co L a) (Co L a) ℂ) = _ from (place_select (L:=L) q).symm]; unfold M; rw [Matrix.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,h q hq,Matrix.mul_assoc (place a q i),Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp (hu i)),Matrix.mul_one]
  exact IsUnit.mul_iff.mp (he.symm ▸ isUnit_one) |>.1
omit [Fintype e] in lemma inv {U : Vertex e (Co L a) (Co L a)} {V : Vertex d a a} (h : Rep S U V) (hu : ∀ q∈S,∀ i : Site L, IsUnit (V.base (aliasAt q i))) : Rep S U.inv V.inv := by
  intro q hq l; simp only [Vertex.inv,Vertex.add,Vertex.const,Vertex.mul,Vertex.inc,Vertex.neg,Pi.neg_apply,Pi.add_apply, Pi.zero_apply,Matrix.mul_zero,Matrix.zero_mul,add_zero]; have he := congr_arg ((U.base q)⁻¹ * · * (V.base (aliasAt q l))⁻¹) (h q hq l)
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp (h.unit hq (hu _ hq))),Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp (hu _ hq l)),Matrix.mul_one] at he; exact he.symm
omit [Fintype e] in lemma transpose (hS : ∀ q∈S, -q∈S) (h : Rep S U V) (he : ∀ q∈S,∀ i : Site L, V.base (-aliasAt q i) = V.base (aliasAt (-q) (-i))) : Rep S U.transpose V.transpose := by
  intro q hq i
  apply transpose_injective
  rw [Vertex.transpose, transpose_mul,transpose_mul, transpose_transpose, select_opposite,Matrix.smul_mul]; rw [Vertex.transpose, transpose_transpose,select_opposite,Matrix.mul_smul, h.realize (hS q hq),he q hq]
  rw [Matrix.mul_sum,Fintype.sum_eq_single (-i) (fun j hj => ?_)]
  · dsimp [channel,matrixMulLinear]; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,basis_pair,if_pos rfl,Matrix.one_mul]
  dsimp [channel,matrixMulLinear]; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,basis_pair,if_neg (Ne.symm hj),Matrix.zero_mul,Matrix.zero_mul]
end Rep
end YM.Push.Loops.Block
