import YM.Push.LOCAL_SPLITTING.Merge


/-!
# Cavity left by a distinguished gas component

Disjointness on *the very same* complete supports and vacuum labels; exact coverage of
all flags outside the component's support (even when the inventory inside is empty).
An unforced gas component marked in the first-system identity is not yet an insertion
in the exponential: it must still avoid every selected final vacuum gas support. In
particular a good output mask on the component does NOT exempt it from testing overlaps.
Here is the corresponding subtraction, through precisely `Local.Slots.pack`, with no
change of the existing alphabet. A forced component uses `coat` instead. These are
pointwise identities, still before estimates on the new component weights themselves.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Planned.Forced
open Lattice Wilson RG Source Function Filter MeasureTheory Push.Local 
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {n : Side} {G : Gauge} (A : Activities G n) (B : BudgetPoint) (X : Support n)

def ExteriorOK (U : Config G n) (b : Finset ℕ) : Prop :=
    Separate A b ∧ (∀ i∈b, Disjoint X (Push.Local.patch A i)) ∧ b.biUnion (flagsFor A) = flags B.threshold U \ X

def outsideTerm (U : Config G n) (b : Finset ℕ) : ℝ := if ExteriorOK A B X U b then ∏ i∈b,A.K i U else 0

def outsideGas (U : Config G n) := ∑' b, outsideTerm A B X U b

variable {A B}







section Removing
variable {ι : Type*} {Z : ι → Support n} (S : Slots A Z)



variable (A B Z)



variable {A Z}





variable {B}








end Removing
end YM.Planned.Forced
