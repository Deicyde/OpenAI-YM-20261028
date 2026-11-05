import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import YM.RG.History

/-! # Moment-rich Fourier iterations on the regulated side -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory VectorFourier
open scoped Topology ContDiff BigOperators InnerProductSpace FourierTransform Real

/-- sufficient absolute convergence to take ALL fixed orders -/
structure Profit (f:E4→ℂ) : Prop where
  seen : AEStronglyMeasurable f
  moment (j:ℕ) : Integrable (fun p:E4 => ‖p‖^j * ‖f p‖)
namespace Profit
variable {f g:E4→ℂ}








end Profit


end YM.Further.FreeCovariance.KP
