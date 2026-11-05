import Mathlib.Analysis.Fourier.FourierTransformDeriv
import YM.Further.FREE_COVARIANCE_KP.KP.Plain
import YM.Further.FREE_COVARIANCE_KP.KP.Snow


/-! # Cost of the inverse Fourier integral of the symbol error -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory VectorFourier
open scoped Topology ContDiff BigOperators InnerProductSpace FourierTransform Real

variable {ι : Type*} {f : ι→E4→ℂ} {l : ℕ}




def dump := ∫ p,arctic p








/-- Positive i sign; no normalizing constant yet. -/
def feed (f:E4→ℂ) (x : E4) := ∫ p:E4, song x p*f p




/-- L so `-L` with Mathlib uses OUR sign. -/
def height := (2*Real.pi)⁻¹







end YM.Further.FreeCovariance.KP
