import YM.Next.EXTRACTION.Basis
import YM.Next.FREE_KERNELS.Switch
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Polynomial
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Powers

/-!
# Power estimates of the read sup and pricing the polynomial after bend

N log coordinate count (larger than K in these applications,
possibly empty). Does not use a large likelihood or a tilted joint
precision. Keep total coefficient budget.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Arc
open AnalyticBridge.LocalGaussianLaws  
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote  Extra.Iteration.Scales MeasureTheory Local
open Primitives.GCC.LocalPolynomial (Script)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

-- cost of unguarded fluctuations by all living coordinates. FIRST
-- term for empty register. Use on one fixed step.
def heat (N K : ℕ) (E : ℝ) (n : ℕ) := 1+(N:ℝ)*(powerBill K E n * kiln K E)

section power
variable {α I : Type} [MeasurableSpace α] [Fintype I] {μ : Measure α}



end power

section scaffold
variable {tier : ℕ} {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

-- X of this gauge's exact comparison

end scaffold

-- polynomial with actual coefficient norm
section point
open MvPolynomial
variable {I : Type} [Fintype I] (p : Script I) {d : ℕ} (hp : p.totalDegree ≤ d) (y z : Gaussian.Vec I)

private def pointConst (z : Gaussian.Vec I) (i : I) := (C (z i:ℂ):Script (Fin 0))
omit [Fintype I] in
private lemma read_point : aeval (pointConst z) p=C (peval p z) := by
  have he : aeval (pointConst z) = ((Algebra.ofId ℂ (Script (Fin 0))).comp (aeval (fun i => (z i:ℂ)))) := by ext; simp [pointConst]
  rw [he]; rfl



include hp

end point

section poly
open Primitives.GCC.LocalPolynomial (Script)
variable {α J I : Type} [MeasurableSpace α] [Fintype I] [Fintype J] {μ : Measure α}


end poly
end YM.PhysicalNext.WeightedGaussianMarginal45C.Arc
