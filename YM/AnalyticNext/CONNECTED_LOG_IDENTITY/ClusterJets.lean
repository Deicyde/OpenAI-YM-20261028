import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Work.A05.Read
import YM.Work.A07


set_option warningAsError false

/-!
# Reserve & reanchor for emission

Derivative bill at the second-log stage. This charges powers
on the WHOLE log label, through constituent cover reserves earned
at the stronger exponent. No differentiating any $g_X$ at a flag
boundary, merely paying emittable E labels. Unlike the input hit and
K estimates, this consumes actual Healthy-germ derivative income
on each $u_X$ in its own normalized directions at its own anchor.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Jets
open Lattice RG Wilson Finset Filter Function
       
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {ι : Type*}
variable (p : BudgetPoint)





variable (X : ι → Support n) (o : ι → Site n) (u : Config G n → ι → ℝ) (b : ι → ℝ)






/-- The input regular receipt needed here. Applies also to u singleton
values that do not vanish at identity or whose Hessian participates in
the future kinetic reset. -/
structure Smooth : Prop where
  anchors i : o i∈X i
  placed i : p.Regular (X i) (fun V => u V i)
  cost i : p.supBounds (o i) (X i) (fun V => u V i) (b i)







end YM.Push.LogIdentity.Jets
