import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Symmetric Taylor coefficients

Used to identify radial jets , and reusable for equality of
Taylor data on the reconstruction side. No analyticity assumption on a
function beyond the actual multilinear forms here. Multilinear arity zero allowed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Tensor

open ContinuousMultilinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E F) in
abbrev T (j : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F

instance (j : ℕ) [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] : FiniteDimensional ℝ (T E F j) := by
  let C : T E F j →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin j => E) F :=
    { toFun := toMultilinearMap, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  exact FiniteDimensional.of_injective C toMultilinearMap_injective

variable {j : ℕ}

def Sym (A : T E F j) := ∀ v : Fin j → E, ∀ s : Equiv.Perm (Fin j), A (v ∘ s) = A v

def diagonal (A : T E F j) : E → F := fun x => A (fun _ => x)

lemma same_slot (A : T E F (j+1)) (h : Sym A) (x v : E) (i : Fin (j+1)) :
    A (Function.update (fun _ ↦ x) i v) = A (Fin.cons v (fun _ => x)) := by
  rw [← h _ (Equiv.swap 0 i), Function.update_comp_equiv]
  congr 1
  simp only [Equiv.symm_swap, Equiv.swap_apply_right]
  ext k
  refine Fin.cases ?_ (fun n ↦ ?_) k <;> simp

lemma differential_diagonal (A : T E F (j+1)) (h : Sym A) (x v : E) :
    fderiv ℝ (diagonal A) x v = (j+1) • A.curryLeft v (fun _ => x) := by
  let c : E →L[ℝ] Fin (j+1) → E := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id _ _
  have hd : HasFDerivAt (diagonal A) ((A.linearDeriv (fun _ => x)).comp c) x :=
    (A.hasFDerivAt (c x)).comp x c.hasFDerivAt
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, linearDeriv_apply]
  change ∑ i : Fin (j+1), A (Function.update _ i v) = _
  simp_rw [same_slot A h x]
  simp

lemma freeze_sym (A : T E F (j+1)) (h : Sym A) (x : E) : Sym (A.curryLeft x) := by
  intro v s
  rw [curryLeft_apply, curryLeft_apply, ← h (Fin.cons x v) (Equiv.Perm.decomposeFin.symm (0,s))]
  congr 1
  ext i
  refine Fin.cases ?_ (fun n ↦ ?_) i <;> simp [Equiv.Perm.decomposeFin_symm_apply_succ]

lemma ext_diag (A B : T E F j) (ha : Sym A) (hb : Sym B) (he : diagonal A = diagonal B) : A = B := by
  induction j with
  | zero =>
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show v = fun _ ↦ 0 from Subsingleton.elim ..]
    exact congr_fun he 0
  | succ j ih =>
    have hc : A.curryLeft = B.curryLeft := by
      apply ContinuousLinearMap.ext
      intro x
      refine ih _ _ (freeze_sym A ha x) (freeze_sym B hb x) (funext fun y ↦ ?_)
      have hh := (differential_diagonal A ha y x).symm.trans (he ▸ differential_diagonal B hb y x)
      rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at hh
      exact (smul_right_injective F (show ((j+1 : ℕ) : ℝ) ≠ 0 by positivity)) hh
    rw [← uncurry_curryLeft A, hc, uncurry_curryLeft]
end YM.Tensor
