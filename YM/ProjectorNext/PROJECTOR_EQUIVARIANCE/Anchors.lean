import YM.Push.CUTOFF_PROJECTORS.Equations


/-!
# Actually moving with aligned anchors

Packet/ComesFrom uses the transfers at anchor zero. Can genuinely run
**these** transfers, coefficients and operator covariances up the aligned
offsets with no further equivariance hypothesis. Not claiming the same for a
new calibration or arbitrary non-embedded offsets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Labels Lattice Wilson RG Source MeasureTheory Push.CutoffProjectors
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {p N d : ℕ} {C : Family G} {E : Packet C d N p} {S : Finset Cover}

lemma always_room (C : Family G) (m p : ℕ) : 2 ≤ (C.side m p).val := by
  have h := C.path.levels.fits.sizeT m p
  change 100*_ ≤ (C.side m p).val at h; omega


end YM.ProjectorNext.Equivariance
