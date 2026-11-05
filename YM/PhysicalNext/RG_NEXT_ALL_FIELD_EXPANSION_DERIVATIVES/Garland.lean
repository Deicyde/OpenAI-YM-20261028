import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mercury
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pattern
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Loops
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.ORDERED_AFFINE_2B.Journeys
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.Canopy




/-! # Layout of signed/translational variants with native inventories

Coexistence even if old Moves (including zero-priced labels) obtained by
noncanonical choice for each R (e.g., reps at different x in `Curve`).
Fixed tape holds `R` asking ancestor-reg etc. continuity; use population
lemmas at *exactly* replay, not unrelated proposed scenes. Numbers price
soft word anchoring carefully later; keep projected fine seat on singleton E.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Bower.Clover
open Function Filter Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree Push Push.SectorMeasure Oriented
open Precision Finset MeasureTheory Matrix ConnectedActivityE6 ConnectedActivityE6.Shell ConnectedActivityE6.Channel ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Census ConnectedActivityE6.Coat ConnectedActivityE6.Matter
open AbsoluteSums Next.Fluctuations Work.F03 AnalyticBridge.VerifiedReset
open InterpolatedSecantsFc (Payload replay)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] forestFintype
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (R : Rep G f) (T : Tube G S) (l : ℕ) (x W w a : ℝ) (N : ChartRatio G) (χ : Chi) (p : BudgetPoint)

abbrev Thin := {v:Molecule S // (ground R T l (radiusB x) v).Nonempty ∧ (roster v).flags=∅}
abbrev Thick := {v:Molecule S // (ground R T l (radiusB x) v).Nonempty ∧ (roster v).flags.Nonempty}
abbrev Regular := Seat c × Thin R T l x
abbrev Hard := Seat c × Thick R T l x
instance : Countable (Molecule S) := by
  let X (p : Molecule S) : Finset (Stores S) × Finset ℕ × ListsAt c f := (p.toLeft,p.toRight.toLeft,p.toRight.toRight.toRight,p.toRight.toRight.toLeft)
  have h (p : Molecule S) : issue (X p).1 (X p).2.1 (X p).2.2=p := by ext i; rcases i with i|i|i|i <;> simp [X,issue]
  exact (show Injective X from fun i j he=> (h i).symm.trans (by rw [he]; exact h j)).countable



abbrev classic {R T l x} (i : Thin (G:=G) R (S:=S) T l x) := ground R T l (radiusB x) i.val
abbrev workers {R T l x} (i : Thick (G:=G) R (S:=S) T l x) := ground R T l (radiusB x) i.val
abbrev inheritFlags {R T l x} (i : Thick (G:=G) R (S:=S) T l x) := (roster i.val).flags







def plaque : PreAtlas.Pane G c (Regular R T l x) (Hard R T l x) where
  X i := Seat.spread i.1 (classic i.2)
  full i := i.2.property.1.image _
  forces i := ⟨Seat.spread i.1 (workers i.2), Seat.spread i.1 (inheritFlags i.2), i.2.property.2.image _,
    image_subset_image (Matter.range_flags i.2.val), fun _=> True⟩
 -- no subset

abbrev scale (c : Side) := (Fintype.card (Seat c):ℝ)⁻¹


def pile (i : Thin R T l x) (V : Config G c) := allot (fun F=> Blaze.Stained.fringe (scene T F V x w χ) W a i.val R N l)
def batch : PreAtlas.Palette G c (Regular R T l x) (Hard R T l x) where
  u i V:= scale c * pile R T l x W w a N χ i.2 (Seat.view i.1 V)
  d i V:= scale c * lumen R T x w W a l N χ i.2.val (Seat.view i.1 V)



def fashion (s : Signed) (b : Site c) : (plaque R T l x).Clubs s b where
  free := Equiv.prodCongr (Seat.move s b) (Equiv.refl _)
  locations i := (Seat.spread_move (x:=i.fst) s b _).trans (PreAtlas.side_slid ..).symm
  forced := ⟨Equiv.prodCongr (Seat.move s b) (Equiv.refl _), fun i=> (Seat.spread_move (x:=i.fst) s b _).trans (PreAtlas.side_slid ..).symm,
    fun i=> (Seat.spread_move (x:=i.fst) s b _).trans (PreAtlas.side_slid ..).symm, fun _ _=> Iff.rfl⟩
 -- elaborate

end YM.PhysicalNext.Bower.Clover
