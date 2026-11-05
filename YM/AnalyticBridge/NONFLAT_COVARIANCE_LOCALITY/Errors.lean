import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Panels

/-!
# Window errors

Keep the exponential with both jet roots (hence also for the transpose),
including for the correction which really uses the inverse of *C*, not the
Gram. Keep every occurrence charge incurred when inverting again.
No trace or polynomial summation yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Matrix Function Filter Lattice RG Wilson Pressure Tree
open Next.SectorChange Next.SectorChange.Schur
open FreeResolvent Mark TestD Window
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c : Side} {α : Type} [Fintype α] [DecidableEq α]

/-- Estimates referencing the same per-column approximants as the full
covariance (not independent compressors). `PolePrices` for the actual
varying windows, also discrepancy/error receipts. -/
structure PaneEarnings (x : ℝ) (a : α → Site c) (W : α → Set α)
    (F : Coord G c → Matrix α α ℝ) (n : ℕ) (s γ C : ℝ) (z : Coord G c) : Prop where
  poles u : 0 ≤ u → PolePrices u a (fun x => panes W u (F x)) n s C z
  residual u : 0 ≤ u → Tagged a a n s (C*remits γ x*drain u) (fun y => overruns W u (F y)) z
  accuracy u : 0 ≤ u → Tagged a a n s (C*remits γ x*drain u^2) ((fun y => panes W u (F y))-action F u) z

variable {x C M s Y t z γ V : ℝ} {F : Coord G c → Matrix α α ℝ} {W : α → Set α}
    {p : α → Site c} {b : Coord G c} {n : ℕ}







namespace PaneEarnings
variable (h : PaneEarnings x p W F n s γ C b)
include h






end PaneEarnings

/-- `S` with actual finite-range entries. -/
def deviation (A C : Matrix α α ℝ) := A*C - 1





end YM.AnalyticBridge.NonflatCovarianceLocality
