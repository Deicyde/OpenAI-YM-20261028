import Mathlib.Analysis.Complex.CauchyIntegral
import YM.CellFourier.Mesh
import YM.Laurent.Rune


/-!
# , last analytic step

Quadrature on the **normalized** BZ (Rim param by `walk`, radian q). True
harmonic-inclusive mesh. Does NOT require external parameters vary
analytically; can be any (even two independently chosen mesh characters)
and made uniform simply via the bound. Vane requires complex periodicity on
whole strip; establish this BEFORE e.g. dephased expressions, not
implied by agreement at mesh points for arbitrary interpolations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Laurent Bloch RG MeasureTheory Complex UnitAddTorus
open scoped Topology BigOperators








/-- Infinite BZ integral with probability Haar measure, hence no extra
`(2π)^(-4)`; `veils u 0 (dress Axis x)` agrees with `u (walk Axis x)`
for Vane (`Vane.steps`). Don't use for non-periodic off-grid rules; also need
integrability of the actual integrand (`zone_integrable`). -/
def zoneMean (u : Momentum → ℂ) : ℂ := ∫ a, veils u 0 a ∂globe Axis





variable {n : Side}









/-- Vane.issues cost of the Fourier-series conversion. Define after
selecting strip (could be post-L), not upon learning mesh or external tests. -/
def quadCost (η K : ℝ) : ℝ := K*(2*((1+η/3)/(η/3)))^4


end YM.Primitives.TwoWave
