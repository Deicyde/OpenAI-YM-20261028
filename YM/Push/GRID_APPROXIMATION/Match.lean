import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Work.A07
import YM.Work.B06

/-!
# Matching coordinates for a k birth

Why this doesn't just call `C.Makes` twice: the coarser cutoff k
would in general use a DIFFERENT history/β. Use B70 cone algebra
`G08` with a view exposing exactly the N cutoff of interest, even in k
queries. Then match at an admitted l (which can be lower than the final
h-grid stopping level for the replica estimate). Need explicit INPUT of
the corresponding Paper.Clocks/vowel budgets for births from k along the
existing H.rep N (`view`), through l. Not assuming full old/new products
can be propagated because singles can.

The collated upper bounds at fixed k can help supply actual `Supplies`;
no claim about rates simultaneous as k increases/doing the whole launch.
Real assumption for old coordinates at match l made exact (not promised for
all l of an arbitrary `Based`; if using its own reference then it is the
literal target). Also no claiming its sign recurrence pair estimate from
this algebra alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox.Match
open RG Source Wilson Cells Lattice Labels Bid MeasureTheory Function Filter Finset Ac Marker Overlay 
open scoped Topology BigOperators
variable {G : Gauge} (H : History G)

/-- Adapt an API quantifying in history, *not* a selected new history for
phase or another estimate. The levels are definitionally H's, all rep
constants and addresses used for the probes are H.rep N at those levels. -/
def view (N : ℕ) : History G := { H with rep := fun _ p m => H.rep N p m }

def ladder : ℕ → ℝ
  | 0 => 1
  | m+1 => ladder m * (H.levels.params (m+1)).columns




variable {H} {l m d k N p : ℕ} {F : Labels.Frame G d} {S : SectionData F} {A : Hol G}





variable (C : Family G)

/-- The actual old normalization for the one-source comparison. Coefficients
at match l computed in the given factory. -/
def old (i N p : ℕ) (v : C.label d) :=
   (C.factory d N p).entries i ((C.factory d N p).terminal.symm v)







end YM.Push.GridApprox.Match
