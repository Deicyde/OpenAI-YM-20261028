import YM.Push.RELAY_MARK.Cutoff

/-!
# Where the equation image actually sits at N in top weighted columns

Grade here means `t` grading.

Nothing requires the orientation intertwiner
remain filtered in *engineering degree* (never used to commute blocking
in Paper.Clocks).

Keep every polynomial projection through d instead.

No
assertion that same budgets suffice for loop or future block alignment estimates.

Offer before scheduling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Bid Next.Foundations Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {d j N p : ℕ} {R : Weave G} {C : Family G}



def up (R : Label G d →ₗ[ℂ] Label G d) := ∀ (p : Label G d) (k : ℕ) , p.val∈floorSlots k → (R p).val∈floorSlots k

-- extraction retains both directions
structure Graded (R : Weave G) : Prop where
  heads d : up (R d).toLinearMap
  tails d : up (R d).symm.toLinearMap
  triangular (d : ℕ) (m) (p : Label G d) : m∈code d → p∈ Grade m → ((R d p).val-p.val)∈above m
  transfer (a) (m) (p : Label G a) : m∈code a → p∈ Grade m → (((R a).symm p).val-p.val)∈above m -- NOT kinetic transfer













/- per direction full weighted letter / cutoff scale -/











end YM.Push.Mark
