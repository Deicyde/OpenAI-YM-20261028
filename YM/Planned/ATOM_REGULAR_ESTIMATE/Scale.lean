import YM.Planned.ATOM_REGULAR_ESTIMATE.Localization
import YM.Push.LOCAL_SPLITTING.Raw

/-!
Produce the actual one-step physical-scale raw insertion, pre-projection,
principal AND secondary income. Require a reserve on the output later to
accommodate moved-indicator terms. Costs across levels/periods remain those
of the original representations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Census
open Function Filter Lattice Wilson RG MeasureTheory Push.Local Source Next.Foundations
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {n m : Side} {i r d e : ℕ} (F : Labels.Frame G d)
  {S : StepData m n} {B : BudgetPoint} {o : Site n} {X : Support n} {Y : Rep G n} {R : Rep G m} {C ε δ v : ℝ}
  {f : Config G n → ℂ} {c : ℝ}

/-- Multiply the FULL marked singleton output by `L^d`. (Even companions
packed into the existing K address.) Use these same evaluated fields for the
canonical extraction. -/
def marked (D : Census S B X R) (f : Config G n → ℂ) : Raw F m where
  seed := 0
  bulk i := ((S.patch.L.val:ℂ)^d) • D.gain i f
  forced i := ((S.patch.L.val:ℂ)^d) • (D.fare i).collect B f

variable {F} {D : Census S Y.p X R}







/-- Quantitative inputs for applying the raw regular estimate. -/
structure Admission (S : StepData m n) (B P : BudgetPoint) (d r : ℕ) : Prop where
  size : 2 ≤ n.val
  period : 100 * (P.B+1) ≤ m.val
  ratio : 4 ≤ S.ratio.count.val
  health : B.B ≤ 2 * P.B
  weights : Umbered B S.ratio.count
  trade : Across B P r S.ratio.count
  order : d+1 ≤ P.order
  through : P.order ≤ B.order

 



end YM.Planned.AtomRegular.Census
