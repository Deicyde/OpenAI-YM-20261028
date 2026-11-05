import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.PSeries
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Tower
import YM.Next.ROTATIONS.Thaw
import YM.Next.SCHEDULE.Dues
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Broad
import YM.Work.B05


/-!
Chart prices after taking sector radii small (does not require making the
next good threshold any smaller than already needed for these patches once
put in the delay bills). Derivatives and changes of the *variable-scale*
log extension cost O(d²) per link in a/d units including positive orders
and the top jet variation; cutoff alone costs O(1), not close to one in sup.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Push.SectorMeasure Precision
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

section ordinary
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ ψ : E → F} {x y : E}


def dilate (φ : E → F) (t : ℝ) (x : E) := φ (t • x)


lemma dilate_smooth {t : ℝ} {k : ℕ} (h : ContDiffAt ℝ (↑k) φ (t • x)) : ContDiffAt ℝ (↑k) (dilate φ t) x :=
  h.comp (f:=fun x => t • x) x (contDiffAt_id.const_smul t)




end ordinary



variable {G : Gauge} (q : Chi)
lemma broad_scale {d : ℝ} (h : 0<d) (u : ℝ) (x : G.Color) : broad q (u*d) (d • x) = broad q u x := by
  unfold broad Chi.innerShare
  rw [norm_smul,Real.norm_of_nonneg h.le,mul_comm u,mul_div_mul_left _ _ h.ne']












structure GuardCost (Z : ChartRatio G) (k : ℕ) (d C : ℝ) : Prop where
  pos : 0<d
  paid : 1≤C
  base (x y : G.Color) : Towers k (broad q 1) (broad q 1) x y C (C*‖x-y‖)
  log (x y : G.Color) : Towers k (dilate (logGuard q Z d) d) (dilate (logGuard q Z d) d) x y (C*d^2) (C*d^2*‖x-y‖)


end YM.AnalyticBridge.MarginalMultiplier3b1d
