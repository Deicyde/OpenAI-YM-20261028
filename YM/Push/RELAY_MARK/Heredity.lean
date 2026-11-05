import YM.Push.RELAY_MARK.Span

/-!
# One weight higher

An optional extra: can keep our exact mark when additionally choosing
nested (literal) sections. Towards transit. The point is to keep
powers under control at each step (slots priority), even for sections extended
to higher d before any budget is instantiated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Labels Wilson Source Lattice RG Bid Next.Foundations Source.Drops
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {d n e : ℕ} {f : Pre G}





-- Terms above k may use higher generation or more factors.








-- raise sons

def bud (G : Gauge) (d : ℕ) : Label G d →ₗ[ℂ] Label G (d+1) := raiseLabel G d.le_succ









end YM.Push.Mark
