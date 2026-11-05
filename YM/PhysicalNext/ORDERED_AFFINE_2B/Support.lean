import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.LocalStation
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.District
import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
import YM.Extra.SOURCE_HISTORIES.Pencil
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.LabelEst
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.JOINT_CALENDAR.Issue
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Filters
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.Push.STRESS_FLUX.Matching
import YM.Push.STRESS_FLUX.Ward
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free
import YM.UVNext.COUPLING_RESET.Reset
import YM.UVNext.FREE_STRESS_CERTIFICATE.Triangle



/-!
# Read sets on the stored arrays (affine F0 stencils)

Supports here are sufficient output-site balls including *all*
possible probes, even when a color is later zero. Numerical radius and
decision radius charged separately. Use full read set in any overlap
application. Arc convention: edge read at its initial site in a ball,
retain also its END (likewise for plaquette reads: all links/incident
locations). See delayed price with extra additive radius in the exports.
This file also tests the hard choices in the actual Rows.source; they
are NOT what we differentiate. Keep A,F etc frozen when taking germs.
Full external/global predicate V∈eligible A is separate, not claimed
to be local at a single occurrence. Keep tree.up and both choice
components in Terrain.Teams (can retain height too in the same set;
never a height sharing argument). Costs x-y only on one Tube/species.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Footprint
open Function Filter Set Lattice Wilson RG Pressure Precision Exterior Tree
open AnalyticBridge AnalyticBridge.Covariance AnalyticBridge.Covariance.Terrain
open AnalyticBridge.LocalGaussianLaws.Lift (copyAgree vBand kickBand zipAt signedAgree)
 
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps
open Push.SectorMeasure Oriented Matrix Pressure.Tube
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f}

def ticketRadius (x : ℝ) := radiusB x/20000

/-- Includes equality-border decisions. This sup is purchased without
assuming the kept branch. `PathData.kept` uses `≤`.
-/
def Ticketed (p : Clip) (x : ℝ) := ∀ k : ℕ, temp x * Real.exp (k/p.relaxation) ≤ 2 → k ≤ ticketRadius x


def coreN (P : Patch) (x : ℝ) := 2*span P x + ticketRadius x + 10



variable {x : ℝ} {V V' : Config G c}
    {A A' : Stores S} {F F' : Forest S.ratio} {k k' : S.Choices}
    {T : Tube G S}










/-- Include *every* possible Frozen read on the queried set. Compare
possibly different structures on the same physical positive bond, not
according to its slot number (which changes with the rest of the torus).
Use `Shared` below for dependence assertions, keeping V and Y roles
distinct even when proving results only at eligible phases. -/
def Preserves (S : StepData c f) {F F' : Forest S.ratio} {A A' : Stores S} {x : ℝ} (o : Site c) (n : ℕ)
    (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A' x F')) :=
    ∀ i j, i.val.val=j.val.val → separation o (S.ratio.parent i.val.val.1) ≤ n → Y i=Y' j

variable {Y : LinkArray G (Frozen A x F)} {Y' : LinkArray G (Frozen A' x F')}
    {d : ℝ} {q : Chi} {o p : Site c} {n m r s : ℕ}
structure Shared (S : StepData c f) {F F' : Forest S.ratio} {A A' : Stores S} {x : ℝ} (o : Site c) (n r : ℕ)
    (k k' : S.Choices) (V V' : Config G c)
    (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A' x F')) : Prop where
  team : Teams S o n r F F' A A' k k' V V'
  holds : Preserves S o n Y Y'

lemma Shared.zone (h : Shared S o n r k k' V V' Y Y') (he : separation o p+m≤n) (ht : separation o p+s≤r) :
    Shared S p m s k k' V V' Y Y' := ⟨h.team.zone he ht,fun i j hv hx=> h.holds i j hv
      ((separation_triangle o p _).trans ((Nat.add_le_add_left hx _).trans he))⟩





 -- tape_read may need match
end YM.PhysicalNext.OrderedAffine2B.Footprint
