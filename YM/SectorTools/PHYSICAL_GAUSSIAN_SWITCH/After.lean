import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Gauges
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sale
import YM.Next.MULTISOURCE.Curves
import YM.SectorNext.RECONNECTED_LOCALITY.Gaussian



/-! Store with field-alignment & cut-jet prices on this step. Commit
delay BEFORE Wait/Bar, supports all periods and every eligible level.
No promises on pre-L constants (read post-L purchase, incl polynomial
or exp costs depending on L). Leave charts, flags, tags where they are. -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch.After
open Function Filter Set Matrix MeasureTheory Lattice Wilson RG RG.Supply Precision Exterior Pressure Testing Tree Bid
open Next Next.SectorChange Rows Next.Scheduling
open AnalyticBridge.GaussianFieldAlignment AnalyticBridge.Covariance Sale
open Push.PriceCompiler
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D}
structure Advance where
  M : ℝ
  σ : ℝ
  C : ℝ
  paid : 0<M
  rate : 0<σ
  aff : 0≤C











variable {W : Delays Θ} {Y : Bar W} {I : Wait Y} {P : PostCost D} {Z : ChartRatio G} {K : MapPrices}
    (F : Input.Directed G I Z K P) {r : ℕ → ℕ → Advance} {p : ℕ → ℕ → ℝ} {w a E : ℕ → ℕ → ℝ}


end YM.SectorTools.PhysicalGaussianSwitch.After
