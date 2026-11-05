import YM.Maxwell.Exterior

/-!
# Maxwell+Bianchi shell (Euclidean)

Take ordinary curl jets, no contact terms in covariance.
Real Lie coordinates, equation legs **without conjugation**.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell
open Tensor Analysis Function Set Filter
open scoped ContDiff Topology BigOperators

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Gauge} {j : ℕ}

def onShell (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) : Submodule ℝ (TwoJet F j) where
  carrier := {Q | Q ∈ formSpace j F ∧ ∀ b x, ∑ a : Axis, grad a (diagonal (Q a b)) x = 0}
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, ?_⟩
    intro b z
    change ∑ a : Axis, fderiv ℝ (fun y : E4 => (0:F)) z (basis a) = _
    simp
  add_mem' := by
    rintro x y ⟨hx,h⟩ ⟨hy,H⟩
    refine ⟨Submodule.add_mem _ hx hy, ?_⟩
    intro b z
    have he (a : Axis) : grad a (diagonal ((x+y) a b)) z =
        grad a (diagonal (x a b)) z + grad a (diagonal (y a b)) z := by
      change fderiv ℝ (diagonal (x a b) + diagonal (y a b)) z _ = _
      rw [fderiv_add ((diag_smooth _ ∞).differentiable (by simp) _)
        ((diag_smooth _ ∞).differentiable (by simp) _)]; rfl
    simp_rw [he, Finset.sum_add_distrib, h,H,add_zero]
  smul_mem' := by
    rintro t x ⟨hx,h⟩
    refine ⟨Submodule.smul_mem _ t hx, ?_⟩
    intro b z
    have he (a : Axis) : grad a (diagonal ((t • x) a b)) z = t • grad a (diagonal (x a b)) z := by
      change fderiv ℝ (t • diagonal (x a b)) z _ = _
      rw [fderiv_const_smul ((diag_smooth _ ∞).differentiable (by simp) _)]; rfl
    simp_rw [he, ← Finset.smul_sum, h, smul_zero]

abbrev Shell (G : Gauge) (j : ℕ) := ↥(onShell G.Color j)

def gaugeJet : Shell G j →ₗ[ℝ] Labels.Taylor G j :=
  potential.symm.toLinearMap.comp <| Submodule.inclusion (p := onShell G.Color j) (fun _ h => h.1)

theorem leg_injective : Injective (gaugeJet (G := G) (j := j)) :=
  potential.symm.injective.comp <| Submodule.inclusion_injective _

theorem match_leg (X : Shell G j) : takeCurl (gaugeJet X) = X.val := curl_inverse X.property.1

abbrev Field (F : Type*) := Axis → Axis → E4 → F

/-- Equations on an open patch. -/
structure WaveOn (U : Set E4) (f : Field F) : Prop where
  smooth (a b : Axis) (x : E4) : x ∈ U → ContDiffAt ℝ ∞ (f a b) x
  form (a b : Axis) (x : E4) : x ∈ U → f a b x = - f b a x
  cycle (a b c : Axis) (x : E4) : x ∈ U →
    grad a (f b c) x + grad b (f c a) x + grad c (f a b) x = 0
  divergence (b : Axis) (x : E4) : x ∈ U → ∑ a : Axis, grad a (f a b) x = 0

namespace WaveOn
variable {U : Set E4} {f : Field F}

def nth (A : Field F) (j : ℕ) (z : E4) : TwoJet F j := fun a b => coeff (A a b) j z

theorem nth_smooth (h : WaveOn U f) {x : E4} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (nth f j) x :=
  contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun l => coeff_smooth (h.smooth i l x hx) _

protected theorem jets (Uo : IsOpen U) (h : WaveOn U f) {x : E4} (hx : x ∈ U) :
    nth f j x ∈ onShell F j := by
  have hu := Uo.mem_nhds hx
  constructor
  · constructor
    · intro i l; apply coeff_symm; exact (h.smooth i l x hx).of_le (WithTop.coe_le_coe.mpr le_top)
    · intro i l
      change coeff _ j x = -coeff _ j x
      rw [← neg_coeff]; refine GermCoeff j ?_
      filter_upwards [hu] with y hy
      exact h.form i l y hy
    intro a b c z
    cases j with
    | zero =>
      have he (A : T E4 F 0) (a) : grad a (diagonal A) z = 0 := by
        rw [show diagonal A = fun _ => diagonal A 0 from funext fun _ => congr_arg A (Subsingleton.elim ..)]
        simp [grad,D]
      rw [he, he, he]; simp
    | succ j =>
      have he (a b c) : grad a (diagonal (coeff (f b c) (j+1) x)) z =
          diagonal (coeff (grad a (f b c)) j x) z := slot_lower ((h.smooth b c x hx).of_le (WithTop.coe_le_coe.mpr le_top)) ..
      unfold nth
      rw [he a b c, he b c a, he c a b]
      have hs (a b c) : ContDiffAt ℝ j (grad a (f b c)) x :=
        (grad_smooth _ (h.smooth b c x hx) (m := ∞) (by simp)).of_le (WithTop.coe_le_coe.mpr le_top)
      have hr := coeff_add (show ContDiffAt ℝ j (grad a (f b c)+grad b (f c a)) x from
        (hs a b c).add (hs b c a)) (hs c a b)
      rw [coeff_add (hs a b c) (hs b c a)] at hr
      have hz : grad a (f b c) + grad b (f c a) + grad c (f a b) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hu] with w hw; exact h.cycle a b c w hw
      exact congr_arg (fun A : T E4 F _ => diagonal A z) (hr.symm.trans ((GermCoeff j hz).trans (coeff_zero ..)))
  intro b z
  cases j with
  | zero =>
    have he (A : T E4 F 0) (a) : grad a (diagonal A) z = 0 := by
      rw [show diagonal A = fun _ => diagonal A 0 from funext fun _ => congr_arg A (Subsingleton.elim ..)]
      simp [grad,D]
    simp_rw [he]
    exact Finset.sum_const_zero
  | succ j =>
    have he (a) : grad a (diagonal (coeff (f a b) (j+1) x)) z =
        diagonal (coeff (grad a (f a b)) j x) z := slot_lower ((h.smooth a b x hx).of_le (WithTop.coe_le_coe.mpr le_top)) ..
    simp_rw [nth, he, Tensor.diagonal]
    rw [← sum_apply, ← coeff_sum]
    · have ht : (∑ a : Axis, grad a (f a b)) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hu] with w hw
        rw [Finset.sum_apply]; exact h.divergence b w hw
      rw [GermCoeff j ht, coeff_zero]; rfl
    intro i _
    exact (grad_smooth i (h.smooth i b x hx) (m := ∞) (by simp)).of_le (WithTop.coe_le_coe.mpr le_top)

end WaveOn
end YM.Maxwell
