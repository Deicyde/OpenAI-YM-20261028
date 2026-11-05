import YM.Extra.FREE_DETECTOR_ALGEBRA.Forest

set_option warningAsError false

/-!
# Colliding OPE coefficient as lower label

Directional notation; no basis change for reading the polynomials.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels SphereTest
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {j k n : ℕ} {x y : E4}

abbrev token (k : ℕ) (i : Fin (legDim G k)) : Slot G := ⟨k,i⟩

/-- Select only terms tested at one homogeneous jet **order**. -/
def deltaOp (X : Sol G.Color k) : Derivation ℂ (WickPol G) (WickPol G) :=
    ∑ i : Fin (legDim G k), ((coordinateLeg (token k i) X:ℝ):ℂ) • MvPolynomial.pderiv (token k i)

theorem delta_eval (X : Sol G.Color k) (p : WickPol G) : deltaOp X p =
    ∑ i : Fin (legDim G k), ((coordinateLeg (token k i) X:ℝ):ℂ) • MvPolynomial.pderiv (token k i) p := by
  unfold deltaOp; rw [deriv_apply_sum]; rfl

def brake (p : WickPol G) (j : ℕ) : Sol G.Color j →ₗ[ℝ] WickPol G where
  toFun X := deltaOp X p
  map_add' X Y := by simp_rw [delta_eval, _root_.map_add,Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
  map_smul' a X := by
    simp_rw [delta_eval,_root_.map_smul,smul_eq_mul, Complex.ofReal_mul]
    change ∑ i, _= a • (∑ i: Fin (legDim G j),_)
    rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [mul_smul]; exact IsScalarTower.algebraMap_smul (R:=ℝ) (M:=WickPol G) ℂ _ _














end YM.Extra.FD
