import YM.MultiNext.VACUUM_STABILITY.FirstGas

set_option warningAsError false

/-!
# Reference exits are the true analytic singleton derivatives

Useful to compare to a separate but compatible pipeline at the RPaper/RAdvances
port. Unordered absolute convergence charged at even one radius on tested axis suffices.
Includes derivatives of partially restricted sums with this/stronger price.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Windows
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {V I : Type}
variable (B : Brush V G n) (C : Restock V G n) (P : BudgetPoint) (U : Config G n)
variable [Fintype V]

def ray (i : V) (z : ℂ) (x : V) : ℂ := if x=i then z else 0

omit [Fintype V] in
@[simp] lemma ray_nought (i : V) : ray i 0=0 := by funext x; simp [ray]








end YM.Multi.Vacuum.Windows
