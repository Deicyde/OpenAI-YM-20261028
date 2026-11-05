import Mathlib.RingTheory.Nilpotent.Exp
import YM.Extra.MULTISOURCE_BOUNDS.Repeated
import YM.Push.ABSOLUTE_SUMS.Ursell
import YM.Push.CORRECTED_COLUMNS.Program

/-!
# Opening the actual unforced marked comparison gas (I)

Use coefficient of the real-log identities, but at every root of the
numbered step trees. Alphabet of the FIRST marked gas. Distinguish from
producing the actual *unmarked* sector data/first system; need separate
alignment hypothesis of the first system with the reclosed unmarked law.
Not producing estimates at fine derivative order for RMixed here either.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Clusters
open Function Filter Set MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected   Extra.Multi  Repeated 
open Push.AbsoluteSums.Ursell Push.AbsoluteSums.Graph
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {α V : Type*} [Fintype V] [DecidableEq V] {n : Side}



/-- In log uses the (m+1)-th row in m position. Nonunit and unit part
computed together. -/
def ink (X : α → Support n) (W : α → Poly (Marks.all V)) (p : Tuple α) :=
  (↑(Push.AbsoluteSums.Ursell.coefficient (blocked X) p.2 / ((p.1+1).factorial:ℝ)):ℂ) •
     ∏ i, W (p.2 i)




end YM.Further.ThresholdSourceRestart.Clusters
