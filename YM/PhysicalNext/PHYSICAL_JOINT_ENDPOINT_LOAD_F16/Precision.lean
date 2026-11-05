import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Programme
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Currency
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.InRoom
import YM.Extra.ITERATION_NO_LOSS.Pre
import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.Next.MAXWELL.Det
import YM.Progress.STATIONARY_SCENES.Dispatch
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.SectorNext.VACUUM_NORMALIZATION.Pivots
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Hosted
import YM.UVNext.COUPLING_RESET.Reset


/-!
# Producing the edge ticket hypotheses of the hK bill, on the actual Gram system

Use `shelves`, not redoing the physical ordered-V-jet estimate. In this lane
the exact Gaussian prescription is `fog` (B70's endpoint version of Ewindow).
Never requiring another kernel or recalculating geometry on Z. We estimate
on the full identity completion (includes all positive fine bonds and all
colors) even if eventually pricing an active piece of these expressions.
No omission of harmonic contributions. (There is no free N0 in this bill.)
Stay at correct output flags and differentiate only the fixed-geometry germs.
No claim about derivatives of stand-alone flags or across a sector change.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.EndpointLoadF16
open Lattice Wilson RG Pressure Pressure.Stores Tree Function Filter Topology Next.SectorChange Set
open FreeResolvent Affine TestD Window Mark Matrix
open SelectedOrderedKernels  NoHole AnalyticBridge.LocalGaussian
open Next.SectorChange.Wisps
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {k p B : ℕ} {o : Site c}


section physical
variable (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (s : S.Choices)




end physical

section reading
variable {M : ℕ → ℝ} {V : Config G c} {γ a W : ℝ} {bp : BudgetPoint}





def timeCost (G : Gauge) (p k : ℕ) (γ M : ℝ) := ∑ i ∈ Finset.range (k+1),
  |tender G i p (γ/2) 1 (offFee G i * M)|
lemma timeCost_pos (G : Gauge) (p k : ℕ) (γ M : ℝ) : 0 ≤ timeCost G p k γ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
lemma timeEnough (G : Gauge) (p k i : ℕ) (γ M : ℝ) (h : i ≤ k) : tender G i p (γ/2) 1 (offFee G i * M) ≤ timeCost G p k γ M := by
  apply (le_abs_self _).trans
  unfold timeCost; exact Finset.single_le_sum (fun i _ => abs_nonneg (tender G i p (γ/2) 1 (offFee G i * M))) (Finset.mem_range.mpr (by omega))



end reading

section stage

variable {V : Config G c} {H : Tube G S} {s M r g a W x : ℝ} {A : Stores S} {T : Forest S.ratio} {q : S.Choices} {bp : BudgetPoint}




end stage
end YM.PhysicalNext.EndpointLoadF16
