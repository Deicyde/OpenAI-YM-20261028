import YM.PhysicalNext.ORDERED_AFFINE_2B.Till

/-!
# Envelopes of this exact same ledger meeting the post-L halo tariffs

Query/padding overhead in SectorChange ABOVE the numerical ranges is
not optional: Use `Archive` even when testing flags under derivatives,
and pay the `watch * rail` complete supports of every long path
(`Shelter.aboard`, `Currency.deck_cover` etc). Use short entries at
12*B. Zone comparisons are explicit in Shelter, Streams, with `Teams`
including the B-halo geometry calls, every possible shot; Forest and all
tag components. Z's (when used as in Spine) endpoints already within
these full supports; when enumerating physical-sector cases even their
full windows and Z/mass decisions fit in these support radii. Does not
suffice to buy ANY larger activity support automatically.

The per-epoch amplitude below also for y not supplied from a surviving
point, z's held; z factors price separately at their coordinates in Z
portion, not blanket assertion that multiplying determinant logs
by material gives only these overheads. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Trip.Tour
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree
open AnalyticBridge AnalyticBridge.ResetIncome SectorTools.ActualScalar
open AnalyticBridge.Covariance Terrain
open Next Next.Foundations Next.SectorChange SectorNext.Vacuum Whole
open Further Further.CurvedGaussianJets Matrix MeasureTheory Set
open Jets ChangeV Tracks Push.SectorMeasure SectorAffine 
open Footprint.Padded (widen)
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

-- assemble the frozen cost as actual link addresses on same radius,
-- regardless of whether later to be allocated into packets.
def iced (x : ℝ) (A : Stores S) (F : Forest S.ratio) (r : ℝ) (i : Bond f) := if i∉F.trunks ∧ ¬onStage A F x i then -r else 0

lemma ice_home {x : ℝ} {A A' : Stores S} {F F' : Forest S.ratio} {k k' : S.Choices}
    {V V' : Config G c} {i : Bond f} (h : Shelter.Bound (S.ratio.parent i.1) x A A' F F' k k' V V') (r : ℝ) :
    iced x A F r i=iced x A' F' r i := by
  have hi := h.trunk_agrees (i:=i) (by rw [separation_self]; unfold Shelter.readH Footprint.Padded.signalH; omega)
  have hh := h.curtain (i:=i) (x:=x) (by rw [separation_self]; unfold Shelter.readH Footprint.Padded.signalH; omega)
  simp only [iced, hi, hh]

variable {A : Stores S} {V : Config G c} {k : S.Choices} {x d σ : ℝ} {p : Purse} {n q : ℕ} {e : Plate G S} {Pt : Teller G}
    (h : Operates p σ n q e Pt) (R : Rep G f) {l : List (Directions G c)}
include h






end YM.PhysicalNext.OrderedAffine2B.Trip.Tour
