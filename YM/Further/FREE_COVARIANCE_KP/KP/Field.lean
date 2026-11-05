import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import YM.Further.FREE_COVARIANCE_KP.KP.Hill



/-! # Integrate the regulated continuum multiplier -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory VectorFourier GaussianFourier
open scoped Topology ContDiff BigOperators InnerProductSpace FourierTransform Real

/-- normalized in radians. -/
def tally := height^4
def retract (f:E4→ℂ) := fun x => (↑tally:ℂ)*feed f x













end YM.Further.FreeCovariance.KP
