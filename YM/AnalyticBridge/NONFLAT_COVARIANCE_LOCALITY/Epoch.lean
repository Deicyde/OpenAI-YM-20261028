import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Errors

/-!
# Period/patch prices for the window table

Assemble common constants, including one MORE inversion (of the windowed C).
No assumption that previously issued delays cover the service. Entitled inputs:
actual real precision jet costs, symmetry, gap, finite-local counting estimate,
and coverage radius. The sector call buys this with its true D.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Matrix Function Filter Lattice RG Wilson Pressure Tree
open Next.SectorChange Next.SectorChange.Schur
open FreeResolvent Mark TestD Window
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c : Side} {α : Type} [Fintype α] [DecidableEq α]

structure Epoch (p : α → Site c) (W : α → Set α) (x : ℝ)
    (A Q : Coord G c → Matrix α α ℝ) (v : Coord G c) (n : ℕ)
    (t η γ C : ℝ) : Prop where
  identity : Q = fun z => clouded W (A z)
  frame : BoardPrices p A n t C η v
  paper : PaneEarnings x p W A n t γ C v
  covariance : BoardPrices p Q n t C η v
  compressionError : Tagged p p n t (C*remits γ x) (fun z => Q z-(A z)⁻¹) v
  deviations : Tagged p p n t (C*remits γ x) (fun z => deviation (A z) (Q z)) v
  correction : Tagged p p n t (C*remits γ x) (fun z => (Q z)⁻¹-A z) v

-- final rate allowances for two products at fixed arity
private def next (t : ℝ) (n : ℕ) := t/(2*((n+1:ℕ):ℝ))


-- this income is CONTEXTUAL; M,Y,s paid from the installed rows


end YM.AnalyticBridge.NonflatCovarianceLocality
