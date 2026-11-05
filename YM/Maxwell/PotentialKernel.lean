import YM.Maxwell.Shell
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Free potential kernel (radian, 4D)

Off the origin only. No assertion about distributional extension here.
It will only enter the Schwinger comparison under curls at distinct sites.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Maxwell
open Set Function Filter Analysis
open scoped Topology ContDiff BigOperators RealInnerProductSpace

def normal := (4 * Real.pi^2)⁻¹

theorem normal_pos : 0 < normal := by unfold normal; positivity

def Green (x : E4) : ℝ := normal * (‖x‖^2)⁻¹

lemma normalization (x : E4) : Green x = 1 / (4 * Real.pi^2 * ‖x‖^2) := by
  simp [Green, normal]; ring

theorem freeSmooth {x : E4} (h : x ≠ 0) : ContDiffAt ℝ ∞ Green x := by
  unfold Green; have hw := norm_pos_iff.mpr h; exact contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.inv (by dsimp; positivity))

@[simp] theorem even_Green (x : E4) : Green (-x) = Green x := by unfold Green; rw [norm_neg]

def away : Set E4 := {x | x ≠ 0}
lemma open_away : IsOpen away := isOpen_compl_singleton

variable {x : E4}

theorem first_Green (hx : x ≠ 0) (i : Axis) : grad i Green x = -2 * normal * x i * (‖x‖^2)⁻¹^2 := by
  have hw := norm_pos_iff.mpr hx
  have h := ((hasFDerivAt_inv (show ‖x‖^2 ≠ 0 by positivity)).comp x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul normal
  have he := h.fderiv
  change fderiv ℝ Green x = _ at he
  unfold grad D
  rw [he]
  simp [two_smul]
  rw [← real_inner_comm x, basis_inner]
  ring

theorem second_Green (hx : x ≠ 0) (i j : Axis) :
    grad j (grad i Green) x = -2 * normal * (basis j i) * (‖x‖^2)⁻¹^2 +
      8 * normal * (x j * x i) * (‖x‖^2)⁻¹^3 := by
  have hw := norm_pos_iff.mpr hx
  let g : E4 → ℝ := fun y => -2 * normal * y i * (‖y‖^2)⁻¹^2
  have he : grad i Green =ᶠ[𝓝 x] g := by
    filter_upwards [open_away.mem_nhds (show x ∈ away from hx)] with y hy
    exact first_Green hy i
  change D (basis j) _ _ = _
  rw [GermD _ he]
  have h := ( (compAxis i).hasFDerivAt.const_mul (-2 * normal)).mul
    (((hasFDerivAt_inv (show ‖x‖^2 ≠ 0 by positivity)).comp x
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt).pow 2)
  have hd := h.fderiv; change fderiv ℝ g x = _ at hd
  rw [D,hd]
  simp [two_smul, -basis_eq, compAxis]
  rw [← real_inner_comm x, basis_inner]
  ring

/-- Laplacian vanishes on the open patch. -/
theorem harmonic (hx : x ≠ 0) : ∑ i : Axis, grad i (grad i Green) x = 0 := by
  have hw := norm_pos_iff.mpr hx
  simp only [second_Green hx, basis_eq, ↓reduceIte, mul_one, ← sq]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.sum_mul,
    ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  field_simp
  ring

/- Ordinary differentiated radial identities. -/
theorem gradGradientSmooth (hx : x ≠ 0) (i : Axis) : ContDiffAt ℝ ∞ (grad i Green) x :=
  grad_smooth i (freeSmooth hx) (by simp)
theorem HessSmooth (hx : x ≠ 0) (i j : Axis) : ContDiffAt ℝ ∞ (grad i (grad j Green)) x :=
  grad_smooth i (gradGradientSmooth hx j) (by simp)

theorem grad_sum (f : Axis → E4 → ℝ) (H : ∀ i, ContDiffAt ℝ ∞ (f i) x) (k : Axis) :
    grad k (fun y => ∑ j, f j y) x = ∑ j, grad k (f j) x := by
  unfold grad D
  rw [fderiv_fun_sum (fun i _ => (H i).differentiableAt (by simp)), sum_apply]

theorem Hess_sym (hx : x ≠ 0) (i j : Axis) : grad i (grad j Green) x = grad j (grad i Green) x :=
  grad_comm ((freeSmooth hx).of_le (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from
    WithTop.coe_le_coe.mpr le_top)) ..

theorem harmonic_gradient (hx : x ≠ 0) (i : Axis) : ∑ a : Axis, grad a (grad a (grad i Green)) x = 0 := by
  have he (a b) : grad a (grad b Green) =ᶠ[𝓝 x] grad b (grad a Green) := by
    filter_upwards [open_away.mem_nhds (show x ∈ away from hx)] with y hy
    exact Hess_sym hy ..
  have hw (a) : grad a (grad a (grad i Green)) x = grad i (grad a (grad a Green)) x :=
    (GermD (basis a) (he a i)).trans (grad_comm ((gradGradientSmooth hx _).of_le
      (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) ..)
  simp_rw [hw, ← grad_sum (fun j => grad j (grad j Green)) (fun j => HessSmooth hx j j)]
  have H : (fun y => ∑ a : Axis, grad a (grad a Green) y) =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [open_away.mem_nhds (show x ∈ away from hx)] with y hy
    exact harmonic hy
  exact (GermD (basis i) H).trans (by simp [D])

end YM.Maxwell
