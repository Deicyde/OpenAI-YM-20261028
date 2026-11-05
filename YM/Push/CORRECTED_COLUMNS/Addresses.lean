import YM.Push.CORRECTED_COLUMNS.Program
/-!
# Calibration helpers: origin and literally translated singleton densities

No mixing costs from `C.Makes`.

Before the restart we DO know the
physical singleton insertion density, already unnormalized and INCLUDING
markers on masked-out configurations.

Instead
prove equalities directly for the pushed densities.

Applicable on exactly
the A placements through N to k. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Issue
open RG Marker Cells Wilson Lattice MeasureTheory Function
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {r k N p : ℕ} {B : Wire C r k N p} {d : ℕ}

-- pull-equivariance for the actual operator. Parent k-level sites.





def chunk (C : Family G) (v : C.label d) (m N p : ℕ) : Source.Coefficient (C.labels.level d) (C.side m p) :=
    (C.factory d N p).entries m ((C.factory d N p).terminal.symm v)







end YM.Push.Corrected.Issue
