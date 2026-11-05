import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Completed
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Shift

/-!
# A quadratic insertion specified in potential coordinates

Often a proof has the R-letters or source response instead of the
normalized law and wants to compare with the Gaussian one would get by
absorbing that insertion. Here's the comparison (for REAL affine + quadratic
insertions only, no interacting score theorem). `bill` is *exact* even on
p such insertions (p needn't be integer); full and marginal coercivity
conditions proved equivalent for a supported insertion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch.Potential
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment.Relative (trade)
open scoped Topology BigOperators ENNReal
local notation "Covar" => Next.SectorChange.Gaussian.Table
attribute [local instance] shift_probability
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {D B : Covar I} {u : Vec I} {p : ℝ}

def system (D B : Covar I) (p : ℝ) := D⁻¹+p • B
def bill (D B : Covar I) (u : Vec I) (p : ℝ) :=
  Real.sqrt ((system D B p)⁻¹).det / Real.sqrt D.det * Real.exp (quad (system D B p)⁻¹ (p • u) / 2)









-- convenience: produce the comparison Gaussian instead of assuming it.
def tilted (D B : Covar I) := (system D B 1)⁻¹














section marginal
 
variable {e : J ↪ I}


end marginal
end YM.SectorTools.PhysicalGaussianSwitch.Potential
