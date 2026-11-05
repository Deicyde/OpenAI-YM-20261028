import YM.Extra.WILSON_STARTUP.Cake
import YM.Work.H02


/-! # Initial compulsory receipts at additional finite support exponent -/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Start
open Function Filter RG Lattice Wilson Ovens Ovens.Pipes Padded Bid
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {c : Clip} {b : BudgetPoint} {l σ κ γ w β : ℝ}

def expand (b : BudgetPoint) : BudgetPoint := { b with supportExponent := b.supportExponent+8, exponent_pos := by linarith [b.exponent_pos] }

theorem expandK (hc : Decent c b) (ht : b.threshold ≤ threshold G b.order b.power) (h : Loan (expand b) l σ κ γ)
    (hβ : l ≤ β) (hw : Bid.quote κ (Real.exp γ-1) ≤ w) : (presentation G n c b β).activities.KBound (expand b) w := by
  have he := digests (c:=c) (n:=n) (G:=G) (b:=expand b) ⟨hc.direct,hc.radius,hc.cut⟩ ht h hβ le_rfl
  exact Work.H02.answer G n _ _ (enumeration G n) _ _ _ _ w _ hw he (h.buys ⟨hc.direct,hc.radius,hc.cut⟩ hβ)
end YM.WilsonStartup.Start
