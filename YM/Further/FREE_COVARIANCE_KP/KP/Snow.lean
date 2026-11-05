import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import YM.PREC.Stacks




/-! # Outer part with one cut on the scale prescribed by displacement -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace

variable {ι : Type*}
def arctic (p : E4) := ((1+‖p‖)^5)⁻¹























variable {m : ℕ} {f : ι→ E4→ℂ}







end YM.Further.FreeCovariance.KP
