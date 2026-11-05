import Mathlib.Analysis.Complex.ExponentialBounds
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Annual
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Capital

set_option warningAsError false

/-!
# Sum complete E alignment families (even after comparisons)

Transfer lifts by Harvest and buys with a common rate at the B70 clock
(and can restrict those purchases to C-league certified inputs).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Harvest
open Filter Function MeasureTheory RG Marker Wilson Lattice Multi Multi.Couples Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : Gauge} {n : Side} (P : Rep G n)

structure Posters (P : Rep G n) (v : Site n) (M M0 : Pulse G n) (r k : ℝ) where
  Y : ℕ → Support n
  fish : ℕ → Config G n → ℂ
  fee : ℕ → ℝ
  weight i : Weight P.p (Y i) (fish i)
  atPoint i : v∈Y i
  binds i : 0 ≤ fee i ∧ ∀ U, ‖fish i U‖ ≤ fee i
  cap : SumBudget (fun i => burn P.p (r+2) (Y i)*fee i) k
  repairs : M.1=M0.1-(fun U => ∑' i,fish i U) ∧ M.2=M0.2+(fun p U => ∑' i,ballast (Y i) P (fish i) p U)

variable {P} {X x : Support n} {κ σ r k : ℝ} {i : Site n} {M M0 : Pulse G n}
variable (Z : Posters P i M M0 r k)














end YM.AnalyticNext.GridStop.Harvest
