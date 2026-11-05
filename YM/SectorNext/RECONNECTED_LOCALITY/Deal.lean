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
import YM.Org.Input

set_option warningAsError false

/-!
# Ordered left derivative budget

 and 7606. Complex connection labels use this chart calculus elsewhere;
here real operations on local weights. The neighborhood argument is the
checker from Foundations/Regular (which has the complex sum certificates),
lifted to the product calculation. Healthy is **closed** & outer masks don't
propagate through the inner increment when proving existence of a derivative!
Thus as there, PROVE the extra germ smoothness instead from B.Regular's
ContDiffAt. Keep order of the derivative lists.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
namespace Deal

open Function Filter RG Lattice Wilson 
open scoped Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c : Side}












/-- All splits into left & right ordered hands, repetitions kept. -/
def spreads {ι : Type*} : List ι → List (List ι × List ι)
  | [] => [([],[])]
  | i::is => (spreads is).map (fun p => (i::p.1,p.2)) ++ (spreads is).map (fun p => (p.1,i::p.2))

variable {ι : Type*}

















end Deal
end YM.SectorNext.Reconnect
