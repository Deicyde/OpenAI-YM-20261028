import YM.MultiNext.VACUUM_STABILITY.MergeShape

set_option warningAsError false

/-! Actual complex exponent and merger identity at finite volume. Keep occurrences and
sum over *label* subsets. Finiteness of volume is used via Packs at exit; not pricing with volume
for any uniform result. -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Rejoin.Hearth
open RG Lattice Wilson Filter Finset Function MeasureTheory Text  Syllable Corona Alternatives
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I J : Type*} {n : Side}



lemma union_sum {α β K : Type*} [NormedAddCommGroup K] {f : α → K} {g : β → K} (hf : Summable f) (hg : Summable g) :
    Summable (Sum.elim f g) := (HasSum.sum (f:=Sum.elim f g) hf.hasSum hg.hasSum).summable



variable (D : Hearth n I J)

def embers (L : Support n) (w : Color I J → ℂ) (p : D.Piece) :=
    if D.ground p.val ∩ L=D.tags p.val then ∏ i∈p.val, w i else 0



























end YM.Multi.Vacuum.Rejoin.Hearth
