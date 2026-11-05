import YM.Next.UV_STRESS.Across
import YM.Work.A05.Read





/-!
# Same-history consumer on the red inputs

A05 on the one persistent curve, and B04 reads wired also at every further F.
Price lower estimate version (`Plates`,`Invoice`,`Granular`) vs weaker
physical boundary in Foundation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Cells Spec
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {S : Table C.book} {W : DiffPlan S}
variable (T : MaxwellData C)





open YM.Spin





abbrev Flags (C : Family G) := ((Bel C.book).Tag) ⊕ (Axis × Axis)


def terminal (X : Scaling S) (J : S.Stress) (k : ℕ) (x : Flags C) : S.Tag := x.elim (panels (isoPanel X k))
    (fun i => ⟨4,(↑((X.xi k)⁻¹ * X.r k^4):ℂ) • J i.1 i.2⟩)


end YM.Next.UVStress
