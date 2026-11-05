import YM.Next.FOUNDATIONS.LinkBounds
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Critical

/-!
# Flat critical graph mixed Jet = our trace bill
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Function Matrix Filter
open AnalyticNext.CalendarScene AnalyticNext.CalendarScene.Jets
open scoped BigOperators Classical ContDiff Topology
variable {n : Side} {k : ℕ} {α β : Type} [Fintype α] [Fintype β]

local notation "E" => Board
variable {S U : E α n ℝ × E β n ℝ →ℝ} {ρ : E α n ℝ→ E β n ℝ}
    {I : Invoices α β n ℝ}

/-- matrix in whole joint Hessian conventions (near the stationary graph).
Congruences near zero with physical slice block needed. -/
def vertical (S : E α n ℝ × E β n ℝ→ℝ) (x : E α n ℝ × E β n ℝ) : Matrix (Leaf n β) (Leaf n β) ℝ :=
    of fun i j=> J2 S x (0,spot i) (0,spot j)



lemma vertical_flat (h : ContDiffAt ℝ ω S 0) : (base (reprint S 1)).submatrix (peg α) (peg α)=vertical S 0:=by
  ext i j; rw [Matrix.submatrix_apply,base_at]; unfold reprint extractF
  let L := (desks α β n).toContinuousLinearMap
  change iteratedFDeriv ℝ 2 (S ∘ L) 0 _=J2 S 0 _ _
  rw [Next.Foundations.jets_linear L (h.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]; unfold J2; congr 1
  ext1 l; fin_cases l <;> exact desks_peg _





namespace ClipIn
open Invoices
variable (H : ClipIn I S U ρ)
include H












end ClipIn
end YM.Primitives.TwoWave
