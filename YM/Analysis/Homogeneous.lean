import YM.Analysis.SmoothJets
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-! Homogeneous Taylor coefficients, Euler differentiations and bases -/
set_option autoImplicit false
noncomputable section
namespace YM.Tensor
open Set Function ContinuousMultilinearMap
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {j : ℕ}

variable (A : T E F j)

theorem homogeneous (x : E) (t : ℝ) : diagonal A (t • x) = (t^j) • diagonal A x := by
  have hi := A.map_smul_univ (fun _ => t) (fun _ => x)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hi; exact hi

theorem diag_smooth (m : WithTop ℕ∞) : ContDiff ℝ m (diagonal A) :=
  A.contDiff.comp <| contDiff_pi.mpr fun _ => contDiff_id

theorem Euler (h : Sym A) (x : E) : fderiv ℝ (diagonal A) x x = (j : ℝ) • diagonal A x := by
  cases j with
  | zero =>
    rw [show diagonal A = fun x : E => diagonal A 0 from
      funext fun x => congr_arg A (Subsingleton.elim ..)]
    simp
  | succ n =>
    rw [differential_diagonal A h, Nat.cast_smul_eq_nsmul, curryLeft_apply]
    unfold diagonal
    congr 2
    ext i; refine Fin.cases ?_ (fun k ↦ ?_) i <;> simp

/-- Averaging actual tensors, diagonal preserved. -/
def symmetrize : T E F j :=
  (Fintype.card (Equiv.Perm (Fin j)) : ℝ)⁻¹ • ∑ s : Equiv.Perm (Fin j), A.domDomCongr s

theorem symmetrize_sym : Sym (symmetrize A) := by
  intro v s
  simp only [symmetrize, smul_apply, sum_apply,
    domDomCongr_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun i => ?_
  rfl

@[simp] theorem symmetrize_diagonal (x : E) : diagonal (symmetrize A) x = diagonal A x := by
  simp only [symmetrize, diagonal, smul_apply, sum_apply,
    domDomCongr_apply]
  have h : 0 < Fintype.card (Equiv.Perm (Fin j)) := Fintype.card_pos
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]

/-- Symmetric coefficient multiplying homogeneous form by `ρ`. -/
def added (ρ : E →L[ℝ] ℝ) : T E F (j+1) := symmetrize (ρ.smulRight A).uncurryLeft

theorem added_sym (ρ : E →L[ℝ] ℝ) : Sym (added A ρ) := symmetrize_sym _

@[simp] theorem added_diag (ρ : E →L[ℝ] ℝ) (x : E) :
    diagonal (added A ρ) x = ρ x • diagonal A x := by
  rw [added, symmetrize_diagonal]; rfl

/-- Taylor coefficient, not derivative. -/
def coeff (f : E → F) (j : ℕ) (x : E) : T E F j :=
  (Nat.factorial j : ℝ)⁻¹ • iteratedFDeriv ℝ j f x

theorem coeff_symm {f : E → F} {x : E} (h : ContDiffAt ℝ j f x) : Sym (coeff f j x) := by
  intro _ _; simp only [coeff, smul_apply, Analysis.sym_Jet h _ _]

theorem slot_lower {f : E → F} {x : E} (h : ContDiffAt ℝ (↑(j+1 : ℕ)) f x) (u z : E) :
    Analysis.D u (diagonal (coeff f (j+1) x)) z = diagonal (coeff (Analysis.D u f) j x) z := by
  rw [Analysis.D, differential_diagonal _ (coeff_symm h), curryLeft_apply]
  simp only [coeff, smul_apply, diagonal]
  rw [Analysis.cons_inner h, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    Nat.factorial_succ, Nat.cast_mul]
  congr 1
  field_simp

end YM.Tensor

namespace YM.Tensor
open Set Function ContinuousMultilinearMap
open Analysis
open scoped Topology ContDiff Filter

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {j : ℕ} {f g : E → F} {x : E}

theorem neg_coeff : coeff (-f) j x = -coeff f j x := by
  rw [coeff, coeff, iteratedFDeriv_neg_apply, smul_neg]

theorem coeff_smooth (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) : ContDiffAt ℝ ∞ (fun y => coeff f j y) x :=
  (show ContDiffAt ℝ ∞ (fun _ : E => (Nat.factorial j : ℝ)⁻¹) x from contDiffAt_const).smul (hf.iteratedFDeriv_right (i := j) (m := ∞) (by change ((↑((⊤ : ℕ∞) + (j:ℕ∞)) : WithTop ℕ∞) ≤ _); simp))

theorem GermCoeff (j : ℕ) (h : f =ᶠ[𝓝 x] g) : coeff f j x = coeff g j x := by
  rw [coeff, coeff, (h.iteratedFDeriv ℝ j).eq_of_nhds]

@[simp] theorem coeff_zero (j : ℕ) (x : E) : coeff (fun _ => (0:F)) j x = 0 := by simp [coeff]

theorem coeff_add (hf : ContDiffAt ℝ j f x) (hg : ContDiffAt ℝ j g x) :
    coeff (f+g) j x = coeff f j x + coeff g j x := by
  rw [coeff, coeff, coeff, iteratedFDeriv_add_apply hf hg, smul_add]

theorem coeff_sum {ι : Type*} (j : ℕ) (x : E) (A : ι → E → F) (l : Finset ι) (H : ∀ i ∈ l, ContDiffAt ℝ j (A i) x) :
    coeff (∑ i ∈ l, A i) j x = ∑ i ∈ l, coeff (A i) j x := by
  unfold coeff
  rw [iteratedFDeriv_sum_apply]
  · rw [Finset.smul_sum]
  exact H

theorem D_coeff (hf : ContDiffAt ℝ (↑(j+1 : ℕ)) f x) (u : E) :
    D u (fun y => coeff f j y) x = coeff (D u f) j x := by
  have h := hf.differentiableAt_iteratedFDeriv (m := j) (Nat.cast_lt.mpr j.lt_succ_self)
  apply ContinuousMultilinearMap.ext
  intro v
  have hev := iteratedFDeriv_succ_apply_left (f := f) (x := x) (𝕜 := ℝ) (Fin.cons u v)
  rw [cons_inner hf] at hev
  simp only [Fin.tail_cons, Fin.cons_zero] at hev
  rw [D]
  simp only [coeff, fderiv_fun_const_smul h, smul_apply, hev]

end YM.Tensor
