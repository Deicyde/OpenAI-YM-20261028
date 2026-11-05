import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
import YM.Push.LOCAL_SPLITTING.NoiseJet

/-!
# Rate bill (volume-independent, the actual coefficients/schedule)

Feasible power screen for mixed atoms. Root cover dominates even after
amortization by marker count. Coarse explicit pre-family constants from the
kernel choices and gauge; *moderate* still needs to be paid post-L at this
family. Multiple inputs, dip into the direction-power schedule only ONCE.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.CalibratedMixedHistory.Crude
open RG Function Lattice Wilson Extra.Trajectories Marker Real Finset MeasureTheory
  Overlay Stock Work.G07 Push.Local.Kernel  Filter 
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {H : History G} {k p T u d N j : ℕ} {S : Side} {P : BudgetPoint}














/-- Pre-block charges of the kernel. -/
def allot (H : Levels G) := (1+H.clock.kernel.penalty * pairingNorm G * ‖(1:G.Mat)‖+G.colorScale)






def docket (A : Levels G) := 4000*(1+allot A)






end YM.Planned.CalibratedMixedHistory.Crude
