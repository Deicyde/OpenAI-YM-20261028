import YM.Further.CURVED_GAUSSIAN_JETS.Cut
import YM.Further.CURVED_GAUSSIAN_JETS.Signed

/-!
# Positive gap and quantitative kernel and logdet errors of a cut flat Gram

Definition by direct positive price, true slot cut, curvature and
transport leading rows in each signed path channel (on actual coordinates)
and common noise linearization. Not `Green.actual` retested after changing
branches, nor the Hessian determinant with full paths. `certify` here buys
post-L prices and one *uniform* cut threshold. Can independently later
truncate principal windows (`Fits`). This is before funding an actual sector
(matrix, cuts, orientations, geometry and bounds there); in particular
don't assume equality with an unspecified `B0` in `Ledger`. All endpoints
on actual period, `booked` coefficient computed from *full* roots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Cut
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Wilson Tree RG Precision Work
open Progress.StationaryScenes Bid Exterior FlatTree Bloch Pressure Flat
open Green (link wt Both)
open Rows (Bill)
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {G : Gauge} {c f n : Side}

def metric (W : PathData G) (p : Clip) (N : ℕ) (n : Side) := p.direct • (1: Table (Body 2 n)) + (short W N n).transpose*short W N n




def ambient (W : PathData G) (p : Clip) (N : ℕ) (S : StepData c f) := Rot.average (fun s => Rot.conjugate (Rot.map f s) (K (metric W p N f))) +
    S.kernel.penalty • ((probe S).transpose * probe S)

def base (W : PathData G) (p : Clip) (N : ℕ) (S : StepData c f) (F : Forest S.ratio) := (ambient W p N S).submatrix (link F) (link F)



def toll (w : ℝ) := ((Fintype.card (TypeFace 2) + Fintype.card (TypeFace 1):ℕ):ℝ) * Green.differential w
def expense (C w : ℝ) := Real.exp w*toll w*(3*invoice C w ^2)*toll w*Real.exp w








end YM.Further.CurvedGaussianJets.Cut
