import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Basis constructor for covariances with unbounded Wick degree.
Arity handled uniformly, including constant arity zero. Useful also
for extracting coordinate moments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multilabel
open Module Function
open scoped BigOperators

variable {R ι X : Type*} [CommSemiring R] [AddCommMonoid X] [Module R X]
variable {V : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)]
variable {o : ι → Type*}

variable [Fintype ι]

def ofBasis (B : ∀ i, Basis (o i) R (V i)) (Q : (∀ i, o i) → X) :
    MultilinearMap R V X := by
  classical
  let L (i : ι) : V i ≃ₗ[R] (Π₀ _ : o i, R) := (B i).repr.trans <| finsuppLequivDFinsupp R
  exact ((MultilinearMap.fromDFinsuppEquiv o R) (fun p => MultilinearMap.piRingEquiv (Q p))).compLinearMap
    fun i => (L i).toLinearMap

theorem applyBasis (B : ∀ i, Basis (o i) R (V i)) (Q : (∀ i, o i) → X) (v : ∀ i, o i) :
    ofBasis B Q (fun i => B i (v i)) = Q v := by
  classical
  simp only [ofBasis, MultilinearMap.compLinearMap_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, Basis.repr_self]
  simp
  change (∏ _ : ι, (1:R)) • Q v = _
  simp

theorem expansion [DecidableEq ι] (B : ∀ i, Basis (o i) R (V i)) (T : MultilinearMap R V X)
    (v : ∀ i, V i) :
    T v = ∑ e ∈ Fintype.piFinset (fun i => ((B i).repr (v i)).support),
      (∏ i, (B i).repr (v i) (e i)) • (T fun i => B i (e i)) := by
  classical
  have ht (i) : ∑ j ∈ ((B i).repr (v i)).support, ((B i).repr (v i)) j • B i j = v i :=
    (B i).linearCombination_repr _
  conv_lhs => rw [← funext ht]
  rw [MultilinearMap.map_sum_finset]
  exact Finset.sum_congr rfl fun e _ => T.map_smul_univ _ _
end YM.Multilabel
