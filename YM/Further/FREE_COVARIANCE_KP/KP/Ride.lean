import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import YM.CellFourier.Mesh
import YM.Maxwell.Exterior

/-! # Compose any fixed number of the endpoint axes. Actual derivatives
rather than Taylor coefficients here. Restore factorials at probe use. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Maxwell
open scoped Topology ContDiff BigOperators InnerProductSpace
section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
def ride : List Axis → (E4→F) → E4 → F
 | [],f => f
 | i::A,f => ride A (grad i f)

def cyclists : (A : List Axis) → Fin A.length → E4
 | [] => fun i => i.elim0
 | i::A => Fin.cons (basis i) (cyclists A)

variable {f g : E4→F} {x : E4}






end











end YM.Further.FreeCovariance.KP
