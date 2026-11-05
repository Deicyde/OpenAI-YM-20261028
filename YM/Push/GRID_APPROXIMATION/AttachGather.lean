import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Work.A07

/-!
# Exact regrouping at the k birth

Countable old support, finite marker names, no implicit divisions by
old density. Include even dormant terms & aggregate old summands by
mode/base address. Need spare addresses; pair of supports/inventory
used in the same rep. Based in part on the `Ac.Parts` argument already
used for a **different**, real unmarked reindexing in `Work.H01`.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Push.GridApprox.Attach
open RG Lattice Wilson Cells MeasureTheory Measure Function Filter Finset Ac Marker Overlay 
open scoped Topology BigOperators
variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}
    {P : Rep G n} {a : Bands R P} {I : Plan a} (T : Spares I) [Nonempty V]





/-- Collection identity uses `Parts` only on finite *actual selections*. -/
def raw (I : Plan a) (s : Finset (Alphabet V)) (U : Config G n) :=
    a.packet s.toLeft U * ∏ i∈s.toRight, leaf I (Sum.inr i) U



variable {T}



















section final
variable {δ κ u c d b : ℝ} {w : V → ℝ}
variable (hr : P.activities.Valid P.p δ κ) (ha : a.Active) (ht : a.Radial w u c d b)

private local instance : IsTopologicalSemiring (Poly R) := ⟨⟩

/- Countable old packets, summable before comparing distributions.
Finite product with new attachments may be empty and may vanish. -/







end final
end YM.Push.GridApprox.Attach
