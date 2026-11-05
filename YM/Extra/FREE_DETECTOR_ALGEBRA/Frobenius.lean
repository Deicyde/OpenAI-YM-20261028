import YM.Extra.FREE_DETECTOR_ALGEBRA.Solutions

set_option warningAsError false

/-!
# Tensor duality for the one-leg detector problem

The sums defining the Riesz maps in this file have **both orders** a,b and
sum over **ordered** directional slots. We do NOT identify this Frobenius
norm with the norm mathlib uses on the underlying Banach spaces.
On `G.Color` the inner product used is exactly the real physical one with
normalization `(-1/G.repDim) trace`: `Gauge.trace_color`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

abbrev Dirs (j : ℕ) := Fin j → Axis

def dir {j : ℕ} (v : Dirs j) (i : Fin j) : E4 := basis (v i)

theorem dir_cons {j : ℕ} (a : Axis) (s : Dirs j) : dir (Fin.cons a s) = Fin.cons (basis a) (dir s) := by
  funext i; refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

theorem sum_dirs {A : Type*} [AddCommMonoid A] {j : ℕ} (f : Dirs (j+1) → A) :
    ∑ v, f v = ∑ a : Axis, ∑ v : Dirs j, f (Fin.cons a v) := by
  let e := Fin.consEquiv (fun _ : Fin (j+1) => Axis)
  rw [← Fintype.sum_prod_type (fun p : Axis × Dirs j => f (Fin.cons p.1 p.2))]
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

variable {F : Type*} [NormedAddCommGroup F]

lemma tensor_ext [NormedSpace ℝ F] {j : ℕ} {A B : Tensor.T E4 F j}
    (h : ∀ I : Dirs j, A (dir I) = B (dir I)) : A = B := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun Axis ℝ).toBasis) ?_
  intro I
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
  change A (dir I) = B (dir I); exact h I

variable [InnerProductSpace ℝ F] {j : ℕ}

/-- Frobenius pairing of one tensor. -/
def dotDir : T E4 F j →ₗ[ℝ] T E4 F j →ₗ[ℝ] ℝ where
  toFun A :=
    { toFun := fun B => ∑ I : Dirs j, ⟪A (dir I), B (dir I)⟫
      map_add' := by intro B C; simp [inner_add_right,Finset.sum_add_distrib]
      map_smul' := by intro b B; simp [real_inner_smul_right,Finset.mul_sum] }
  map_add' A B := by
    ext C
    simp [inner_add_left,Finset.sum_add_distrib]
  map_smul' a B := by ext C; simp [real_inner_smul_left,Finset.mul_sum]

theorem dotDir_eval (A B : T E4 F j) : dotDir A B = ∑ I : Dirs j, ⟪A (dir I), B (dir I)⟫ := rfl

theorem dotDir_symm (A B : T E4 F j) : dotDir A B = dotDir B A := by
  simp only [dotDir_eval]
  exact Finset.sum_congr rfl fun _ _ => real_inner_comm ..

theorem dotDir_nonneg (A : T E4 F j) : 0 ≤ dotDir A A := by
  simp only [dotDir_eval]
  exact Finset.sum_nonneg fun _ _ => real_inner_self_nonneg

@[simp] theorem dotDir_zero_iff {A : T E4 F j} : dotDir A A = 0 ↔ A = 0 := by
  rw [dotDir_eval, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => real_inner_self_nonneg)]
  refine ⟨fun h => tensor_ext (fun I => ?_),?_⟩
  · exact inner_self_eq_zero.mp (h I (Finset.mem_univ _))
  · rintro rfl I _; simp

/-- Frobenius of all tensors. -/
def dotF : TwoJet F j →ₗ[ℝ] TwoJet F j →ₗ[ℝ] ℝ where
  toFun P :=
    { toFun Q := ∑ a : Axis, ∑ b : Axis, dotDir (P a b) (Q a b)
      map_add' := by intro B C; simp [Finset.sum_add_distrib]
      map_smul' := by intro b B; simp [Finset.mul_sum] }
  map_add' A B := by ext C; simp [Finset.sum_add_distrib]
  map_smul' a B := by ext C; simp [Finset.mul_sum]

theorem dotF_eval (P Q : TwoJet F j) : dotF P Q = ∑ a : Axis, ∑ b : Axis, dotDir (P a b) (Q a b) := rfl

theorem dotF_symm (P Q : TwoJet F j) : dotF P Q = dotF Q P := by
  simp only [dotF_eval]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => dotDir_symm ..

theorem dotF_nonneg (P : TwoJet F j) : 0 ≤ dotF P P := by
  simp only [dotF_eval]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dotDir_nonneg _

@[simp] theorem dotF_zero_iff {P : TwoJet F j} : dotF P P = 0 ↔ P = 0 := by
  rw [dotF_eval, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => dotDir_nonneg _)]
  refine ⟨fun h => funext (fun a => funext (fun b => ?_)),?_⟩
  · exact dotDir_zero_iff.mp <| (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => dotDir_nonneg (P a b))).mp (h a (Finset.mem_univ _)) b (Finset.mem_univ _)
  · rintro rfl i _; simp

theorem dotF_pos {P : TwoJet F j} : P ≠ 0 → 0 < dotF P P := fun h =>
  lt_of_le_of_ne (dotF_nonneg P) (Ne.symm (mt dotF_zero_iff.mp h))

def solProd (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (j : ℕ) : Sol F j →ₗ[ℝ] Sol F j →ₗ[ℝ] ℝ where
  toFun P := (dotF P.val).comp (onShell F j).subtype
  map_add' P Q := by ext R; exact LinearMap.congr_fun (map_add dotF P.val Q.val) R.val
  map_smul' a P := by ext R; exact LinearMap.congr_fun (map_smul dotF a P.val) R.val

theorem solProd_injective : Injective (solProd F j) := by
  apply LinearMap.ker_eq_bot.mp
  refine LinearMap.ker_eq_bot'.mpr fun x hx => ?_
  have h : dotF x.val x.val = 0 := LinearMap.congr_fun hx x
  exact Subtype.ext (dotF_zero_iff.mp h)

def dualSol (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (j : ℕ) :
    Sol F j ≃ₗ[ℝ] Module.Dual ℝ (Sol F j) := LinearEquiv.ofBijective (solProd F j)
      ⟨solProd_injective,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq ..).symm).mp solProd_injective⟩

theorem dualSol_val [FiniteDimensional ℝ F] (P Q : Sol F j) : dualSol F j P Q = dotF P.val Q.val := rfl

/-- Orthogonal projection without opening any local norm instance. -/
def asSol [FiniteDimensional ℝ F] : TwoJet F j →ₗ[ℝ] Sol F j :=
  (dualSol F j).symm.toLinearMap.comp <| LinearMap.flip ((LinearMap.flip dotF).comp
    (onShell F j).subtype)

theorem asSol_duality [FiniteDimensional ℝ F] (P : TwoJet F j) (Q : Sol F j) :
    dualSol F j (asSol P) Q = dotF P Q.val := by
  simp only [asSol,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]; rfl

@[simp] theorem asSol_self [FiniteDimensional ℝ F] (P : Sol F j) : asSol P.val = P := by
  apply (dualSol F j).injective
  exact LinearMap.ext fun Q => asSol_duality P.val Q
end YM.Extra.FD
