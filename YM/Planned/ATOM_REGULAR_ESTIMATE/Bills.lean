import YM.Next.SCHEDULE.Support
import YM.Planned.ATOM_REGULAR_ESTIMATE.Localization

/-! Currency of the component estimates at pre-L exponents and the ratio &
halos actually committed to. Post-L powers named. No coordinates or gain
from the sector estimates assumed in these arithmetic lemmas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter Lattice RG Push.Local Census Next.Scheduling
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n m : Side} {B P : BudgetPoint} {X : Support n} {c C ε : ℝ} {r e k : ℕ} {q : Ratio m n}

namespace Rates

def cap (e : ℕ) (A : ℝ) := ∑' i, Next.Scheduling.decay e (A/4) i



def tip (L : Side) := (L.val:ℝ)^((3:ℝ)⁻¹)
def slide (L : Side) (A : ℝ) := Real.exp (-(A/2)*tip L)

/-- Pre-L earnings factor, only 1/L leading and large-support tail left. -/
def headBill (G : Gauge) (L : Side) (k d r : ℕ) (C M P : ℝ) :=
  Real.exp (phaseBase r P) * C *
    (centralCharge G k d * (L.val:ℝ)⁻¹ + regularCharge k * (L.val:ℝ)^d * slide L M)













private def pay (B : BudgetPoint) (X : Support n) := Real.exp (-(B.supportExponent/2)*(coverNumber B.B X:ℝ))







end Rates
end YM.Planned.AtomRegular
