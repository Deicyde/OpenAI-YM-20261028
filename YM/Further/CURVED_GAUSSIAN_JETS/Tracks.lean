import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import YM.Further.CURVED_GAUSSIAN_JETS.Algebra
import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Next.SCHEDULE.Melt
import YM.Org.Theatre

/-!
# Keeping actual ordered chain labels in the determinant and C⁻¹-A formulas

Repeated indices allowed; each complete entry function always at the SAME
configuration and shared-tag argument. All colors counting. The directed
endpoint test for a diagonal or a precision coefficient is only applied at
collection. Don't require a nonreturning route, or identify reversed paths.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Tracks
open Matrix Function Filter  Lattice RG Wilson Precision
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommSemiring R] {d : ℕ}

abbrev Run (I : Type*) (d : ℕ) := Fin (d+1) → I
def fare (p : Run I d) (M : Fin d → Matrix I I R) := ∏ i : Fin d, M i (p i.castSucc) (p i.succ)
lemma fare_zero (p : Run I 0) (M : Fin 0 → Matrix I I R) : fare p M = 1 := Finset.prod_empty 
lemma fare_next (p : Run I (d+1)) (M : Fin (d+1) → Matrix I I R) : fare p M=M 0 (p 0) (Fin.tail p 0)*fare (Fin.tail p) (Fin.tail M) := by unfold fare; rw [Fin.prod_univ_succ]; rfl

def engine (M : Fin d → Table I) := (List.ofFn M).prod
lemma engine_zero (M : Fin 0 → Table I) : engine M = 1 := rfl
lemma engine_next (M : Fin (d+1) → Table I) : engine M=M 0 * engine (Fin.tail M) := by unfold engine; rw [List.ofFn_succ,List.prod_cons]; rfl
lemma engine_rear (M : Fin (d+1) → Table I) : engine M=engine (Fin.init M)*M (Fin.last d) := by unfold engine; rw [List.ofFn_succ', List.concat_eq_append,List.prod_append,List.prod_singleton]; rfl
lemma engine_pow (M : Table I) : engine (fun _ : Fin d=> M)=M^d := by rw [engine,List.ofFn_const, List.prod_replicate]

def tag (M : Table I) (u v : I) := Matrix.single u v (M u v)
def reserve (p : Run I d) (M : Fin d → Table I) := engine fun i : Fin d=> Tracks.tag (M i) (p i.castSucc) (p i.succ)

lemma bought (p : Run I d) (M : Fin d → Table I) : reserve p M (p 0) (p (Fin.last _)) = fare p M := by
  induction d with
  | zero => rw [reserve,engine_zero,fare_zero,Fin.last_zero,Matrix.one_apply_eq]
  | succ d ih =>
    rw [reserve,engine_next,Matrix.mul_apply,fare_next,Finset.sum_eq_single_of_mem (Fin.tail p 0) (Finset.mem_univ _) ?h]
    · change Tracks.tag (M 0) (p 0) _ (p 0) _ * reserve (Fin.tail p) (Fin.tail M) (Fin.tail p 0) (Fin.tail p (Fin.last _)) = _
      simpa only [Tracks.tag, single_apply, true_and, if_pos (show (p (0:Fin (d+1)).succ=Fin.tail p 0) from rfl)] using! congr_arg (M 0 (p 0) (Fin.tail p 0) * ·) (ih (Fin.tail p) (Fin.tail M))
    intro i _ hi
    simp only [zero_mul,if_false,and_false,Tracks.tag,single_apply,show p (0:Fin (d+1)).succ=Fin.tail p 0 from rfl,Ne.symm hi]

lemma all_trips (g : Run I d → ℝ) : ∑ i, g i = ∑ x, ∑ z, g (Fin.cons x z) := by
  rw [← (Fin.consEquiv fun _ : Fin (d+1) => I).sum_comp, Fintype.sum_prod_type]; rfl
lemma fixed_trip (g : Run I d → ℝ) (x : I) : ∑ p, (if p 0=x then g p else 0)= ∑ z, g (Fin.cons x z) := by
  rw [all_trips]; simp [Finset.sum_ite_irrel]
lemma from_root (M : Fin d → Table I) (i j : I) : engine M i j = ∑ z : Fin d → I, let p : Run I d := Fin.cons i z; if p (Fin.last _)=j then fare p M else 0 := by
  induction d generalizing i with
  | zero => rw [engine_zero,Fin.last_zero]; simp [Matrix.one_apply,fare_zero]
  | succ d ih => rw [engine_next,Matrix.mul_apply,all_trips]; simp_rw [ih (Fin.tail M),Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _=> ?_
                 change M 0 i x * _ = if (Fin.cons i (Fin.cons (α:=fun _=>I) x y) : Run I (d+1)) (Fin.last (d+1))=j then _ else _
                 rw [show Fin.last (d+1)=(Fin.last d).succ from rfl, Fin.cons_succ,fare_next,Fin.tail_cons,Fin.cons_zero,Fin.cons_zero,mul_ite,mul_zero]

def ends (i j : I) (p : Run I d) (z : ℝ) := if p 0=i ∧ p (Fin.last d)=j then z else 0
lemma engine_entries (M : Fin d → Table I) (i j : I) : engine M i j = ∑ p, ends i j p (fare p M) := by
  rw [from_root M i j]; unfold ends; simpa only [ite_and] using (fixed_trip (fun p : Run I d => if p (Fin.last d)=j then fare p M else 0) i).symm
end YM.Further.CurvedGaussianJets.Tracks
