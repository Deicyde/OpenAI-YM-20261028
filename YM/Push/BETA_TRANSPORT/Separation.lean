import YM.Push.BETA_TRANSPORT.Curve
import YM.Work.F03.Transport

/-!
# Two honest no-flag scalar tests

To pass continuity from an *actual* push and its labelled activities to the
scalar v and coupling of a candidate exact output, hold its path/clip/budget
fixed. For a nonzero Lie algebra and side > 1, two fixed all-good test
configurations separate those two scalars. Direct positive quadratic clipping
dominates both higher path sums (all winding slots included); the loop part
is β-independent. No differentiation in the gauge variables of any flag.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG RG.Activities RG.Shoot MeasureTheory Filter Function Set
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff
variable {n : Side} {G : Gauge} {P : BudgetPoint} {D : PathData G} {A : Clip}

lemma atomSeries_chord {k : ℕ} {F : ℕ → Atom G k} {σ C r : ℝ} (hσ : 0 < σ)
    (hB : SumBudget (fun i => (F i).budget σ) C) (hr : 0 ≤ r) {U : Config G n}
    (hu : ∀ p, G.chord (faceValue U p) ≤ r) (x : Site n) :
    ‖PathData.atomSeries F P U x‖ ≤ C * r^k := by
  have he i : ‖(F i).placed P U x‖ ≤ (F i).budget σ * r^k := by
    unfold Atom.placed
    by_cases hg : Healthy P.threshold ((F i).footprint x) U
    · rw [masked_eq _ _ _ _ hg]
      refine (Work.F03.poly_bound _ _ _ ?_).trans (mul_le_mul_of_nonneg_right ((F i).lower_budget σ hσ) (pow_nonneg hr _))
      intro j; rw [Work.F03.atSite_path,G.norm_adjoint]; exact (G.curvature_norm _).trans (hu _)
    rw [masked_ne _ _ _ _ hg,norm_zero]; exact mul_nonneg (hB.1 i) (pow_nonneg hr _)
  have hb := hB.2.1.mul_right (r^k)
  have hs := hb.of_nonneg_of_le (fun _ => norm_nonneg _) he
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum he hb).trans
    (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hB.2.2 (pow_nonneg hr _)))

lemma base_lower (A : Clip) {U : Config G n} (p : Face (Per n)) (hp : G.chord (faceValue U p) ≤ P.threshold) :
    A.direct * G.chord (faceValue U p)^2 / 2 ≤ D.baseTerm A P U p := by
  unfold PathData.baseTerm PathData.clipped
  rw [if_pos hp]; refine le_add_of_nonneg_right ?_; split <;> positivity
lemma flags_empty {U : Config G n} (h : ∀ p, G.chord (faceValue U p) ≤ P.threshold) : flags P.threshold U = ∅ := by
  ext x; simp [flags_spec, not_lt.mpr (h _)]
lemma kinetic_one (D : PathData G) (A : Clip) (P : BudgetPoint) : kinetic D A P (1:Config G n) = 0 := by
  have he (s : Signed) : pull s 0 (1:Config G n) = 1 := by funext e; unfold pull Step.read; split <;> simp
  have hu (b : Face (Per n)) : faceValue (1:Config G n) b = 1 := by simp [faceValue,travel,square]
  have ht (x : Site n) (l : Slot) : l.atSite (1:Config G n) x = 0 := by rw [Work.F03.atSite_path, hu, G.curvature_unit,map_zero]
  have ha (x : Site n) (k : ℕ) [NeZero k] (F : ℕ → Atom G k) : PathData.atomSeries F P (1:Config G n) x = 0 := by
    have h (i : ℕ) : (F i).placed P (1:Config G n) x = 0 := by
      unfold Atom.placed
      by_cases hg : Healthy P.threshold ((F i).footprint x) (1:Config G n)
      · rw [masked_eq _ _ _ _ hg]; simp [Atom.unmasked,Atom.poly,ht,NeZero.ne k]
      rw [masked_ne _ _ _ _ hg]
    simp [PathData.atomSeries,h]
  simp [kinetic,he,PathData.baseTerm,PathData.clipped,hu,P.threshold_pos.le,PathData.ell,PathData.ellTerms,ht,ha]












end YM.Push.BetaTransport
