import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Bind
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Prescription
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.RibbonRise
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Scroll


/-! # Shifting every orientation including tapes for the alpha discrepancy

Conditional on shifts of the actual integrated formulas AND their skeletons. Even
when raw camera choices are carried covariantly under a *changed* Tree that may not
buy this predicate on the current skeleton. No appeal to invariant total in place
of the predicate. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas
open Lattice RG Wilson Function Finset
open Push.LogIdentity Push.AbsoluteSums Ursell Restore Rename
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {n : Side} {G : Gauge} {ι κ : Type} [Countable ι] [Countable κ]
    {M : Pane G n ι κ}

structure Pane.Clubs (M : Pane G n ι κ) (s : Signed) (b : Site n) where
  free : Equiv.Perm ι
  locations i : M.X (free i) = slid s b (M.X i)
  forced : (Scroll.outer M).Shift s b

variable {s : Signed} {b : Site n}
structure Pane.Clubs.Volta (E : M.Clubs s b) (F : Palette G n ι κ) : Prop where
  free i V : F.u (E.free i) V=F.u i (pull s b V)
  forced : E.forced.sym F.d

namespace Scroll
variable (E : M.Clubs s b)

/-- Use the accepted tuple transformation, keep all endpoints & roots. -/
private def turnZ : Rename.Turn M.X M.Y M.I (fun (_ : Config G n) _ => 0) (fun _ _=>0) 0
    (fun i=> (M.forces i).extraTest) s b :=
  ⟨E.free,E.forced.route,E.locations,E.forced.located,E.forced.owned,fun _ _=>rfl,fun _ _=>rfl,fun _=>rfl,E.forced.takes⟩

def turn : (upcoming M).Shift s b where
  route := (turnZ E).anchorMap
  located i := tuple_area M.X _ E.free E.locations i.1
  turns _ := rfl

def decreed : (errata M).Shift s b where
  route := tuple E.free
  located i := tuple_area M.X _ _ E.locations i



variable {F : Palette G n ι κ} (h : E.Volta F)
include h

end Scroll

section compensation
open AnalyticBridge.CouplingShape
variable (n) (R : PathData G) (p : BudgetPoint) (s : Signed) (b : Site n)
namespace TwoMasks
def insist : (slips R p n).Shift s b where
  route := Around.move Sequence s b
  located i := by
    rw [side_slid]
    rcases i with ⟨o,t,a⟩
    exact Around.carries (o,t,a) s b _

end TwoMasks
namespace Prescription
def expost : (stock n R p).Shift s b where
  route := Equiv.sumCongr (Around.move ℕ s b) <| Equiv.sumCongr (Around.move ℕ s b) <|
    Equiv.sumCongr (Around.move ℕ s b) (TwoMasks.insist n R p s b).route
  located i := by
    have he {k : ℕ} (F : ℕ→ Atom G k) (i : Post n) : (Post.park F (Around.move ℕ s b i)).support=slid s b (Post.park F i).support :=
      (Post.sanctuary F s b i).2.1.trans (side_slid ..).symm
    rcases i with i|i|i|i; exact he R.cubic i; exact he R.quartic i; exact he R.loop i; exact (TwoMasks.insist n R p s b).located i
  turns i := by rcases i with i|i|i|i <;> rfl

end Prescription
end compensation
end YM.PhysicalNext.PreAtlas
