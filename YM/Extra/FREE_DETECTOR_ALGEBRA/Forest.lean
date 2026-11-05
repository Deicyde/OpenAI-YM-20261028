import Mathlib.RingTheory.MvPolynomial
import YM.Extra.FREE_DETECTOR_ALGEBRA.Dilate
import YM.Extra.FREE_DETECTOR_ALGEBRA.Invariant
import YM.Extra.FREE_DETECTOR_ALGEBRA.Radials


set_option warningAsError false

/-!
# Finite generating fields through fixed jet order

Wick products internally, standard compact-color argument on *actual* jet
variables, before trying to generate tests using these fields. Maintain
lengths in the representation; costs of dynamical products/sources not
addressed here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels Submodule MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {j k n : ℕ}

structure Badge (G : Gauge) (j : ℕ) where
  p : WickPol G
  size : ℕ
  ones : 0<size
  grade : ℕ
  f : p ∈ folio G j size
  homogeneous : Exact p grade
  color : secret p











abbrev Members (g : Fin n → Badge G j) (k : ℕ) := (i : Fin n) → ↥(folio G j (k-(g i).size))

def operate (g : Fin n → Badge G j) (k : ℕ) : Members g k →ₗ[ℂ] WickPol G where
  toFun A := ∑ i : Fin n, if (g i).size≤k then (A i).val * (g i).p else 0
  map_add' _ _ := by rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp [add_mul]
  map_smul' t A := by
    change (∑ i : Fin n,_)=t • _
    rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp





def memberInk (g : Fin n→ Badge G j) (k : ℕ) : Members g k →ₗ[ℝ] Members g k →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun v := ∑ i, ink G (u i).val (v i).val
      map_add' a b := by simp [Finset.sum_add_distrib]
      map_smul' t a := by simp [Finset.mul_sum,map_smul] }
  map_add' a b := by ext v; simp [Finset.sum_add_distrib]
  map_smul' t a := by ext v; simp [Finset.mul_sum,map_smul]


end YM.Extra.FD
