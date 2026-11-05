import YM.MultiNext.VACUUM_STABILITY.FirstGas

set_option warningAsError false

/-!
# Windows on a forced ledger

`auditGas` even in wrapping geometry. Used to compare p-aggregates independent of the order
of summation and intermediate merger choices. All internal compatibilities still required
when making the ledger!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Windows
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {I J A : Type*} {n : Side}

-- Including all local flags (actual L). Abbreviate filtering each SERIES INPUT by support.

def tested [Zero A] (M : Support n) (X : I→Support n) (a : I → A) (i : I) := if X i ⊆ M then a i else 0

def auditGas [CommSemiring A] (L M : Support n) (F : Pack n → A) :=
    ∑ s ∈ Pack.clears (M∩L), ∏ i∈s,tested M Pack.zone F i

def Vetted [Zero A] (L : Support n) (F : Pack n → A) := ∀ i, Pack.zone i ∩ L ≠ Pack.flagsAt i → F i=0

-- window inversion by finite triangular extraction




variable (D : Hearth n I J)




end YM.Multi.Vacuum.Windows
