import YM.Progress.CLASSICAL_KIN_RECURSION.Plume
import YM.Progress.CLASSICAL_KIN_RECURSION.WardChart


set_option warningAsError false

/-!
# Ward identities of actual finite-period functions
-/
set_option autoImplicit false
noncomputable section
open Filter Function
namespace YM.Progress.ClassicalKin
open Lattice RG Laurent Exterior Wilson Precision Bid Tensor Spools
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

/-- Use on told analytic *log-link functions*, not on arbitrary flat field
arrays assumed covariant. -/
structure Follows (F : Dir G n→ℝ) : Prop where
  analytic : ContDiffAt ℝ ω F 0
  gauges (g : G.El) : F ∘ (rotatedLog g) =ᶠ[𝓝 0] fun x : Booth G n=> F x.1
  signed (s : Signed) : (fun x : Dir G n=> F (pulled x s)) =ᶠ[𝓝 0] F














variable {T : Dir G n→ℝ} (h : Follows T) {k : ℕ} (hv : Dormant T k)
include h hv
lemma Follows.first (v : Fin k→Booth G n) (g : G.El) :
    coeff T k 0 (fun i=> reflects 1 n g ((v i).1+dColor G n 0 (v i).2)) = coeff T k 0 (fun i=>(v i).1) := by
  have he : coeff (T ∘ rotatedLog g) k 0 v = coeff (T ∘ (ContinuousLinearMap.fst ℝ (Dir G n) (fieldDir G n 0))) k 0 v := by
    rw [GermCoeff k (h.gauges g)]
    rfl
  rw [leading_comp T (rotatedLog g) (h.analytic.of_le le_top) ((laced_smooth g).of_le le_top) (chart_zero g) hv,
    leading_comp T _ (h.analytic.of_le le_top) (ContinuousLinearMap.fst ℝ (Dir G n) (fieldDir G n 0)).contDiff.contDiffAt (map_zero _) hv] at he
  simp only [ContinuousLinearMap.fderiv,spell] at he; exact he

omit h hv in
lemma zero_diff : dColor G n 0 0=0 := by
  have ht (i : G.ColorIndex) : parts G 0 (0:fieldDir G n 0) i=0:=rfl
  ext; simp [dColor,ht]
omit h hv in
lemma plain_ref (v : Dir G n) : reflects 1 n 1 v=v := by ext; simp [reflects]





end YM.Progress.ClassicalKin
