import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Nonnegative sampled kernel tools, complex coordinates

Complex partial order means exact reality as well.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Analysis
open Function Set Filter
open scoped Matrix Topology ComplexOrder ComplexConjugate BigOperators
variable {X : Type*}

/-- Algebraic Gram, no distinctness requirement. -/
def NNKernel (K : X → X → ℂ) : Prop := ∀ m : ℕ, ∀ f : Fin m → X,
  (Matrix.of fun i j => K (f i) (f j)).PosSemidef

namespace NNKernel
variable {K L : X → X → ℂ}

theorem gram (f : X → ℂ) : NNKernel (fun x y => star (f x) * f y) := by
  intro m y
  let v := Matrix.of fun (_ : Unit) (i : Fin m) => f (y i)
  rw [show (Matrix.of _) = vᴴ * v by ext i j; simp [v,Matrix.mul_apply]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma one : NNKernel (fun (_ _ : X) => 1) := by simpa using gram (X := X) (fun _ => 1)
lemma zero : NNKernel (fun (_ _ : X) => 0) := by simpa using gram (X := X) (fun _ => 0)

lemma scaled (H : NNKernel K) {c : ℂ} (hc : 0 ≤ c) : NNKernel fun x y => c*K x y :=
  fun n f => (H n f).smul hc
lemma plus (H : NNKernel K) (h : NNKernel L) : NNKernel fun x y => K x y+L x y :=
  fun n f => (H n f).add (h n f)
lemma times (H : NNKernel K) (h : NNKernel L) : NNKernel fun x y => K x y*L x y :=
  fun n f => (H n f).hadamard (h n f)

lemma adds {ι : Type*} (F : ι → X → X → ℂ) (s : Finset ι) (H : ∀ i ∈ s, NNKernel (F i)) :
    NNKernel (fun x y => ∑ i ∈ s, F i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact zero
  | @insert i s h ih =>
    simp_rw [Finset.sum_insert h]
    exact (H _ (Finset.mem_insert_self ..)).plus (ih fun j hj => H _ (Finset.mem_insert_of_mem hj))

lemma pow (H : NNKernel K) (n : ℕ) : NNKernel fun x y => K x y^n := by
  induction n with
  | zero => simpa using one (X := X)
  | succ n h => simp only [pow_succ]; exact h.times H

lemma titled {M : Type*} (H : NNKernel K) (f : M → X) : NNKernel fun x y => K (f x) (f y) :=
  fun n w => H n (f ∘ w)

lemma sampled (H : NNKernel K) {I : Type*} [Fintype I] (x : I → X) :
    (Matrix.of fun i j => K (x i) (x j)).PosSemidef :=
  let t := Fintype.equivFin I
  have he := (H _ (x ∘ t.symm)).submatrix t
  (show Matrix.submatrix (Matrix.of (fun i j => K ((x ∘ t.symm) i) ((x ∘ t.symm) j))) t t = Matrix.of (fun i j => K (x i) (x j)) from by
    ext; simp) ▸ he

lemma positivity {I : Type*} [Fintype I] (H : NNKernel K) (x : I → X) (c : I → ℂ) :
    0 ≤ ∑ i, ∑ j, star (c i)*K (x i) (x j)*c j := by
  have hv := (H.sampled x).dotProduct_mulVec_nonneg c
  simpa [dotProduct, Matrix.mulVec,Finset.mul_sum,mul_assoc] using hv

theorem criterion (he : ∀ x y, star (K y x)=K x y)
    (H : ∀ m : ℕ, ∀ x : Fin m → X, ∀ c : Fin m → ℂ, 0 ≤ ∑ i, ∑ j, star (c i)*K (x i) (x j)*c j) : NNKernel K := by
  intro m x
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,fun c => ?_⟩
  · ext1 i j; exact he _ _
  · simpa [dotProduct,Matrix.mulVec, Finset.mul_sum, mul_assoc] using H m x c

lemma swaps (H : NNKernel K) (x y) : star (K y x) = K x y :=
  congr_fun (congr_fun (H 2 ![x,y]).1 0) 1

lemma closed (k : ℕ → X → X → ℂ) (H : ∀ i, NNKernel (k i)) (he : ∀ x y,
    Tendsto (fun i => k i x y) atTop (𝓝 (K x y))) : NNKernel K := by
  apply criterion
  · intro x y; exact tendsto_nhds_unique ((continuous_star.continuousAt.tendsto.comp (he y x)).congr'
      (Eventually.of_forall fun i => (H i).swaps x y)) (he x y)
  intro i x c
  refine ge_of_tendsto (x := atTop) (f := fun j : ℕ => ∑ a : Fin i, ∑ b : Fin i, star (c a)* k j (x a) (x b)*c b) ?_
    (Eventually.of_forall fun i => (H i).positivity x c)
  exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ fun j _ => ((he _ _).const_mul _).mul_const _)

lemma exp (H : NNKernel K) : NNKernel (fun x y => Complex.exp (K x y)) := by
  apply closed (K := fun x y => _) (fun n x y => ∑ i ∈ Finset.range n, K x y^i / (Nat.factorial i : ℂ))
  · intro n
    apply adds (fun i x y => K x y^i / (Nat.factorial i : ℂ))
    intro i _
    simpa only [div_eq_mul_inv, mul_comm] using
      (H.pow i).scaled (c := ((Nat.factorial i : ℂ))⁻¹) (by positivity)
  intro x y
  have he := (NormedSpace.expSeries_div_hasSum_exp (K x y)).tendsto_sum_nat
  exact Complex.exp_eq_exp_ℂ ▸ he
end NNKernel
end YM.Analysis
