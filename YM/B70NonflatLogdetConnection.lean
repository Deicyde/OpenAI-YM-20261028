import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Boards
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sale
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Extra.SOURCE_HISTORIES.Pencil
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Extra.WILSON_STARTUP.Overlay
import YM.Next.MULTISOURCE.Curves
import YM.Next.UV_STRESS.Fringe
import YM.Next.WARD_BIN.LabelEst
import YM.Progress.JOINT_CALENDAR.Issue
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.FINITE_DETECTION.Variables
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.RELAY_MARK.Span
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.Push.STRESS_FLUX.Low
import YM.Push.STRESS_FLUX.Matching
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free
import YM.UVNext.COUPLING_RESET.Reset
import YM.UVNext.FREE_STRESS_CERTIFICATE.Triangle


/-!
The existing nonflat precision producer supplies the exact matrix input for
the relative-logdet calculus. All matrices refer to the same Stores/Forest,
field, threshold and window prescription. Reindexing includes identity slots;
it neither replaces the covariance nor differentiates the hard flags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.B70NonflatLogdetConnection

open Function Filter Lattice RG Wilson Pressure Tree Matrix
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Completion
open FreeResolvent FreeResolvent.TestD
open scoped Topology ContDiff Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}
    {P : Patch} {p : Teller G} {x C r σ b η g d : ℝ} {k : ℕ}

theorem full_precision
    (h : AnalyticBridge.Covariance.Deck G p P x C r k σ b η g)
    (T : Tube G S) (hP : S.patch=P) (hT : p.Funds S T)
    (hsize : 100*(1+radiusB x) ≤ c.val)
    (V : Config G c) (t : S.Choices) (A : Stores S) (F : Forest S.ratio)
    (hflags : A.flags=RG.flags (temp x) V)
    (B : Directions G c) (hB : ‖B‖≤r) (hd : d≤σ) :
    Knew (AnalyticBridge.Covariance.meterMark G c d) (native c)
      (AnalyticBridge.RelativeLogdet.Physical.place S)
      AnalyticBridge.Covariance.atom B k σ C η 1
      (fun y => AnalyticBridge.RelativeLogdet.Physical.AFull T A F x (increment V y) t) := by
  classical
  obtain ⟨hpay,hgap,-,-,-⟩ := h S T hP hT hsize V t A F hflags B hB
  have hp := AnalyticBridge.Covariance.activate hpay hgap hd
  let e := sorted A F (x:=x) (G:=G)
  have hs := FreeResolvent.TestD.shrink hp e.symm.injective
  have hplace : AnalyticBridge.Covariance.start (G:=G) (x:=x) A F ∘ e.symm =
      AnalyticBridge.RelativeLogdet.Physical.place S := by
    funext i
    change S.ratio.parent (e (e.symm i)).1.1 = S.ratio.parent i.1.1
    rw [e.apply_symm_apply]
  have hmatrix : limitTo (AnalyticBridge.Covariance.painted T A F t x V) e.symm =
      (fun y => AnalyticBridge.RelativeLogdet.Physical.AFull T A F x (increment V y) t) := by
    funext y
    rfl
  rw [hplace,hmatrix] at hs
  exact hs

end YM.B70NonflatLogdetConnection
