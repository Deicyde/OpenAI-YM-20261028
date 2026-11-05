import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.Further.THRESHOLD_SOURCE_RESTART.Wells

/-!
# No per-site-volume loss through common mask alignment

Unlike the final C-correction these letters need pay only at v. Keep
exponential roots at the requested middle exponent. Restore a strong K
savings after the attachment trees at these weights as well. Handles alpha
larger than the mandatory mask cube even though its unforced contribution
hasn't landed there (orphan). This is prior to radius restoration; the
residual comparison still needs more work/input than the Descent's
output costs alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Function Filter Set MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width Extra.Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {I V α : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    {n : Side} {P : Rep G n} {o : I × V → Site n}
variable {F : Atoms P.p (Marks.all (I×V)) o G α}
variable {a b c l u w : ℝ} {M : ℕ}

namespace Wells
variable (W : Wells F)

def ticket (V : Type*) [Fintype V] (t b : ℝ) (q : ℕ) := Real.exp (t*q)*(Fintype.card V*b)



end Wells






end YM.Further.ThresholdSourceRestart
