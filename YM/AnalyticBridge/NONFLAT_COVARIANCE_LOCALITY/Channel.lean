import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Analysis.Polydisc
import YM.Dash.Scope
import YM.Fields.Spectrum
import YM.Overlay.Supplier
import YM.Ward.PDE
import YM.Work.E03



/-!
# All-order branch prices on the selected stencils

Affording D in the tagged window, including the mixed derivatives of the
Q columns. Does not forget the frame corrections; here we compute the
rows exactly, `facade = pull s 0 (increment (replica S.ratio ...) a)`.
Use `carry` before any estimate to pass real read positions back. No need
to spend for derivatives of a `V`-chosen gauge: hold one gauge
fixed on the whole local proof. No global gauge-smallness assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Filter Function Lattice RG Wilson Pressure Precision Tree 
    
  
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma spin_step (i : Bond c) (s : Signed) : separation (s.act i.1) (sendEdge s 0 i).1 ≤ 1 := by
  unfold sendEdge Step.used; simp only [affine,add_zero]; split
  next hf =>
    simp only [Step.rotate,posDir]
    rw [separation_comm]
    have ht := Work.E03.sep_step (s.act i.1-step (s.perm i.2)) (s.perm i.2)
    rwa [sub_add_cancel] at ht
  next hf => simp









end YM.AnalyticBridge.NonflatCovarianceLocality
