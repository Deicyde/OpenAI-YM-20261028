import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Chalet
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.PhysicalNext.ORDERED_AFFINE_2B.Support
/-!
# Complete support charges: active shift and E η read

Even in zero/no-hit queries, enforce `Shared`, separately from
`matched` or branch validity. From *the same* radii in Terrain/Support,
now for entire entries of mean etc. Stops BEFORE organizing support of
the rest of the multiplier/boundary packets. Anchors here initial
coarse or fine-key PARENT. When retaining flag eligibility also include
the links for all those queried V plaquettes (not letting the stored
flag verdict suffice in a physical bill). Delay lemma leaves additive
room so entire endpoints and witnesses also retained in the full halo.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Footprint
open Function Filter Set Lattice Wilson RG Pressure Precision Exterior Tree
open AnalyticBridge AnalyticBridge.Covariance AnalyticBridge.Covariance.Terrain
 
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Completion
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {S : StepData c f} {x g : ℝ}
    {V V' : Config G c} {A A' : Stores S} {F F' : Forest S.ratio} {k k' : S.Choices}
    {T : Tube G S} {s : Signed} {q : Chi} {d : ℝ} {o : Site c} {n r : ℕ}
    {Y : LinkArray G (Frozen A x F)} {Y' : LinkArray G (Frozen A' x F')}
namespace Padded


def sendN (P : Patch) (x : ℝ) := span P x + coreN P x
def viewN (P : Patch) (x : ℝ) := windowR x + lengthA P x + sendN P x
def allN (P : Patch) (x : ℝ) := lengthA P x + viewN P x
-- number radii plus the whole seed halo (AND tree/decision reads)
def signalH (n : ℕ) (x : ℝ) := n + 10*radiusB x + 8

variable (ht : Ticketed T.low x) (hS : S.patch.Branches S.kernel G)
include ht hS







end Padded


end YM.PhysicalNext.OrderedAffine2B.Footprint
