import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Real.Pi.Bounds
import YM.Push.LOOP_COEFFICIENT.AssemblyReal
import YM.Push.LOOP_COEFFICIENT.ContinuumTrace
import YM.Push.LOOP_COEFFICIENT.Fine.Algebra
import YM.Push.LOOP_COEFFICIENT.Paths.Lead
import YM.Push.LOOP_COEFFICIENT.Paths.Polynomial
import YM.Work.F05.Jacobian

/-!
# Changing both internal endpoint charts on a routed precision
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Metric Lattice Laurent RG Bloch Wilson Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b c d j : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq c]

@[ext] lemma Vertex.ext {a b d : Type} {X Y : Vertex d a b} (h : X.base=Y.base) (h' : X.one=Y.one) (h'' : X.two=Y.two) : X=Y := by cases X; cases Y; congr

namespace Block
@[ext] structure Portal (a : Type) [Fintype a] [DecidableEq a] where
  gate : Momentum → Matrix a a ℂ
  unit q : IsUnit (gate q)

namespace Portal
variable (P : Portal a) (Q : Portal b) (S : Portal c)
  (X X' : Vertex d a b) (Y : Vertex d b c)
lemma unit_transpose {a : Type} [Fintype a] [DecidableEq a] {A : Matrix a a ℂ} (hA : IsUnit A) : IsUnit A.transpose := by simpa [Matrix.isUnit_iff_isUnit_det] using hA
lemma unit_nonsing_inv {a : Type} [Fintype a] [DecidableEq a] {A : Matrix a a ℂ} (hA : IsUnit A) : IsUnit A⁻¹ := IsUnit.mul_iff.mp ((A.nonsing_inv_mul (Matrix.isUnit_iff_isUnit_det _ |>.mp hA)).symm ▸ isUnit_one : IsUnit (A⁻¹*A)) |>.1
lemma right_inv (q) : (P.gate q) * (P.gate q)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp (P.unit q))
lemma left_inv (q) : (P.gate q)⁻¹ * P.gate q = 1 := mul_eq_one_comm.mpr (P.right_inv q)
lemma reinvert (q) : ((P.gate q)⁻¹)⁻¹ = P.gate q := Matrix.inv_eq_right_inv (P.left_inv _)

def dual : Portal a where
  gate q := ((P.gate (-q))⁻¹).transpose
  unit _ := unit_transpose (unit_nonsing_inv (P.unit _))
lemma dual_inv (q) : (P.dual.gate q)⁻¹ = (P.gate (-q)).transpose := by rw [dual,← Matrix.transpose_nonsing_inv,P.reinvert]
@[simp] lemma dual_dual : P.dual.dual = P := by apply Portal.ext; funext q; change ((P.dual.gate (-q))⁻¹).transpose = P.gate q; rw [dual_inv,transpose_transpose,neg_neg]

def reduce (p q : Momentum) : Matrix a b ℂ →ₗ[ℂ] Matrix a b ℂ := ((matrixMulLinear _ _ _ _).flip (Q.gate q)).comp (matrixMulLinear _ _ _ _ (P.gate p)⁻¹)
omit [Fintype c] [DecidableEq c] in lemma reduce_apply (P : Portal a) (Q : Portal b) (s q : Momentum) (X) : reduce P Q s q X = (P.gate s)⁻¹ * X * Q.gate q := rfl
lemma reduce_mul (A B p q s) : reduce P S p q (A*B) = reduce P Q p s A * reduce Q S s q B := by simp only [reduce_apply,Matrix.mul_assoc,← Matrix.mul_assoc (Q.gate s) (Q.gate s)⁻¹, Q.right_inv,Matrix.one_mul]
omit [Fintype c] [DecidableEq c] in
lemma reduce_transpose (A p q) : reduce P.dual Q.dual p q A.transpose = (reduce Q P (-q) (-p) A).transpose := by rw [reduce_apply,reduce_apply,transpose_mul,transpose_mul,dual_inv,Matrix.mul_assoc,dual]
lemma reduce_inv (Q : Portal a) (A p) : reduce Q P p p A⁻¹ = (reduce P Q p p A)⁻¹ := by rw [reduce_apply,reduce_apply,Matrix.mul_inv_rev,Matrix.mul_inv_rev,P.reinvert,Matrix.mul_assoc]


def weigh : Vertex d a b where
  base q := reduce P Q q q (X.base q)
  one q p := (reduce P Q (q+p) q).comp (X.one q p)
  two q p s := (X.two q p s).compr₂ (reduce P Q (q+p+s) q)

omit [Fintype d] in lemma weigh_mul : weigh P S (X.mul Y) = (weigh P Q X).mul (weigh Q S Y) := by
  apply Vertex.ext
  · funext q; apply reduce_mul
  · funext q p; ext1 v; exact ((reduce P S (q+p) q).map_add ..).trans (congr_arg₂ (· + ·) (reduce_mul P Q S _ _ _ _ _) (reduce_mul P Q S _ _ _ _ _))
  funext q p s; apply LinearMap.ext; intro v; apply LinearMap.ext; intro w
  simp only [weigh,Vertex.mul, LinearMap.compr₂_apply,LinearMap.compl₁₂_apply,matrixMulLinear,LinearMap.add_apply,LinearMap.flip_apply,LinearMap.comp_apply,LinearMap.mk₂_apply,map_add]
  congr 2
  · congr 1
    · exact reduce_mul ..
    · rw [add_right_comm q]; exact reduce_mul ..
  · exact reduce_mul ..
  · exact reduce_mul ..

omit [Fintype d] in lemma weigh_transpose : weigh Q.dual P.dual X.transpose = (weigh P Q X).transpose := by
  apply Vertex.ext
  · funext q; apply reduce_transpose
  · funext q p; ext1 v; change reduce _ _ _ _ (_ : Matrix _ _ ℂ).transpose = (reduce P Q _ _ _).transpose; rw [reduce_transpose,show -(q+p)+p=-q by abel]; rfl
  funext q p s; apply LinearMap.ext; intro v; apply LinearMap.ext; intro w; change reduce _ _ _ _ (_ : Matrix _ _ ℂ).transpose = (reduce P Q _ _ _).transpose; rw [reduce_transpose,show -(q+p+s)+p+s=-q by abel]; rfl

omit [Fintype d] in lemma weigh_smul (s : ℂ) : weigh P Q (X.smul s) = (weigh P Q X).smul s := by apply Vertex.ext <;> (ext; simp [weigh,Vertex.smul])
omit [Fintype d] in lemma weigh_add : weigh P Q (X.add X') = (weigh P Q X).add (weigh P Q X') := by apply Vertex.ext <;> (ext; simp [weigh,Vertex.add])
omit [Fintype d] in lemma weigh_neg : weigh P Q X.neg = (weigh P Q X).neg := by apply Vertex.ext <;> (ext; simp [weigh,Vertex.neg])
omit [Fintype d] in lemma weigh_const (f : Momentum → Matrix a b ℂ) : weigh P Q (Vertex.const (d:=d) f) = Vertex.const fun q => reduce P Q q q (f q) := by apply Vertex.ext <;> (ext; simp [weigh,Vertex.const])
omit [Fintype d] in lemma weigh_inc : weigh P Q X.inc = (weigh P Q X).inc := by apply Vertex.ext <;> (ext; simp [weigh,Vertex.inc])
omit [Fintype d] in lemma weigh_inv (Q : Portal a) (X : Vertex d a a) : weigh Q P X.inv = (weigh P Q X).inv := by
  rw [Vertex.inv,Vertex.inv, weigh_add,weigh_add,weigh_mul Q Q P,weigh_mul Q P Q,weigh_mul Q Q P,weigh_mul Q P Q,weigh_mul Q Q P,weigh_mul Q P Q,weigh_neg,weigh_inc,weigh_const]; simp only [reduce_inv]; rfl

def count (a : Type) [Fintype a] [DecidableEq a] : Portal a := ⟨fun _ => 1,fun _ => isUnit_one⟩
@[simp] lemma dual_count : (count a).dual = count a := by unfold count dual; simp
omit [Fintype d] in lemma weigh_id : weigh P P (Vertex.id (d:=d) (a:=a)) = Vertex.id := by simp only [Vertex.id,weigh_const,reduce_apply,Matrix.mul_one,left_inv]
omit [Fintype d] in lemma weigh_pow (X : Vertex d a a) (k : ℕ) : weigh P P (X.pow k) = (weigh P P X).pow k := by induction k <;> simp_all [Vertex.pow,weigh_id,weigh_mul P P P]
end Portal
end YM.Push.Loops.Block
