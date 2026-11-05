import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import YM.Next.FLUCTUATIONS.Covariance
import YM.Next.SCHEDULE.Dues
import YM.Primitives.HAAR_LOG_JETS.Symmetry


/-!
# Cost of the actual broadly protected ratio (`SectorChange`)

Finite-order (not all-orders analytic across the guard), for
all log arrays including every `Active A x F`. `reserve_displaced_price`
applies at fixed center to Gaussian prices. No estimate on Y or any movement
of the center/covariance/support, or across d's. Uses a radius requirement;
see `eventual_aperture` for pricing BEFORE spending a stamped displacement
scale. Not claiming a particular chosen delay already pays it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.HaarLogJets.Guard
open Function Filter Set NormedSpace Metric Precision Matrix Next.SectorChange
open Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {q : Chi} {P : ℝ}





variable {n : ℕ} {d : ℝ} {Z : ChartRatio G}









theorem log_extended_turn (e : G.El) (flip : Bool) (q : Chi) (hd : 0 < d) (hZ : LocalRatio Z) (hr : 4*d < Z.radius) (x : G.Color) :
    logGuard q Z d (if flip then -(G.adjoint e x) else G.adjoint e x)= logGuard q Z d x := by
  have he : ‖(if flip then -(G.adjoint e x) else G.adjoint e x)‖ = ‖x‖ := by split_ifs <;> simp
  simp only [logGuard,broad,he]
  by_cases hx : broad q (2*d) x=0
  · simp only [broad] at hx; simp [hx]
  have hh := broad_span q (by positivity) x hx
  have hx : x∈ball 0 Z.radius := mem_ball_zero_iff.mpr (by linarith)
  have ht : G.adjoint e x ∈ ball 0 Z.radius := by simpa using hx
  split_ifs <;> simp [← Next.SectorChange.ratio_even hZ ht,ratio_adjoint hZ hx]

section arrays
variable {ι : Type} [Fintype ι] (s : Finset ι)









end arrays



end YM.Primitives.HaarLogJets.Guard
