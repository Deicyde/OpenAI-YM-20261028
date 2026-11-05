import Mathlib
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Desk
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sale
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Rebased
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Extra.WEAK_SCALING_ACTLAW.Divergence
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.Eqs
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.CORRECTED_COLUMNS.Recover
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.RELAY_MARK.Span
import YM.Push.STRESS_FLUX.Matching
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Current

/-! Linear bookkeeping at this rank. `Speech` answers with additive
log-chart derivatives. Already includes *their* integral equality before
this step. We take finite linear combinations only. Similarly for its
logdet answers. This code neither assumes integral/sum identities are on
all global sectors nor does manifold DCT.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.EndpointLoadF16.DetLong
open Function Filter Set Lattice RG Wilson
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD SelectedOrderedKernels WardBin.Lies
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {B : Directions G n} {V : Config G n} {L : List (Directions G n)} {j k : ℕ}



abbrev strike (V : Config G n) (B : Directions G n) (f : Config G n → ℝ) (z : List (raw G n)) :=
    jet (ray G n) (SelectedOrderedKernels.over f V) z ((paint G n).symm B)
variable (hB : ∀ i, ‖B i‖ < radius G k)
include hB



variable {α : Type} (Rel : (α→ℝ)→ℝ→ Prop) (E : Set α)

omit hB in
private lemma accum
    (hz : Rel (fun _=>0) 0) (ha : ∀ g h s t, Rel g s→Rel h t→Rel (fun w=>g w+h w) (s+t))
    {ι : Type} (I : Finset ι) (F : ι → α → ℝ) (t : ι→ℝ) (h : ∀ i∈I,Rel (F i) (t i)) :
    Rel (fun w=>∑ i∈I,F i w) (∑ i∈I,t i) := by
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using hz
  | insert i I hi hh =>
    have he := hh (fun i hI=>h i (by simp [hI])); have hp := h i (by simp)
    simp only [Finset.sum_insert hi]; exact ha _ _ _ _ hp he


end YM.PhysicalNext.EndpointLoadF16.DetLong
