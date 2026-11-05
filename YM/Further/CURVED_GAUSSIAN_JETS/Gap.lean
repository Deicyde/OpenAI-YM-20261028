import YM.Further.CURVED_GAUSSIAN_JETS.Algebra
import YM.Progress.STATIONARY_SCENES.SliceGap



/-!
# Actual uncut conditional curvature inverse/bills (no path/Comptroller assumption)

F01 counts and E02 shell theorem supply our gap, tested on a single
(nonempty) real color.

Includes free curvature return covariance from
`Horizon`; the estimates concern true periodic rows not a formal limit
or cover path length.

Need the stated Larger and real metric hypotheses,
no arbitrary reblocking.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Flat
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Wilson Tree RG Precision Work
open Progress.StationaryScenes Bid Exterior  Bloch Pressure
open Green (link wt Both)
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {G : Gauge} {c f n : Side}

def paint {X : Type*} (v : Vec X) (j : G.ColorIndex) (i : X) : G.Color := EuclideanSpace.single j (v i)





variable (S : StepData c f) (F : Forest S.ratio)













end YM.Further.CurvedGaussianJets.Flat
