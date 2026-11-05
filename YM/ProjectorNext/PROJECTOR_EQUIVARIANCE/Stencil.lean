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
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07

/-!
# The local stencil option for physical W: signed-axis operations

Check the operations indicated there for
constructing covariant weights on the actual link arrays.

We only need the
*finite* signed/orientation laws here.

Use literal clover, transported site
fields and iterated centered (half) differences on group arrays.

Not estimates
that their leading holonomy coefficients do what calibration wants, or a
choice of clovers/differences for the rest of the algorithm.

Here legs of W
are linear on the gradients but can be multilinear in such transported
clovers.

Color splitting/agreement with continuum ideal presentation and
combinations of these stencils are separate data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance.Stencil
open Function Filter Lattice Wilson RG Source Labels MeasureTheory 
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

/-- BOTH components of the signed-site filter. Acts on any physically
normalized gradient/color array of left components. -/
def sensor (U : Config G n) (A : Directions G n) (x : Site n) (a : Step) :=
    if a.neg then - G.adjoint ((U (a.used x))⁻¹) (A (a.used x)) else A (a.used x)









/-- Take signed-site half difference, not sum. -/
def aperture (G : Gauge) (i : Axis) (f : Step → G.Color) :=
  (1/2 : ℝ) • (f (posDir i)-f (negDir i))

def sign (s : Signed) (i : Axis) : ℝ := if s.flip i then -1 else 1





/-- Apply the prescribed site difference to *an adjoint field* read
at neighboring sites. No change of basepoint or sign after halving. -/
def centered (U : Config G n) (f : Site n → G.Color) (i : Axis) (x : Site n) :=
  aperture G i fun a => G.adjoint (a.read U x) (f (x+a.vec))



/-- Gradient leg,  (`site difference` here subtracts a *negative*
orientation component, not the positive component at the previous site).
If also normalizing by inverse of the leading Wilson coefficient multiply by
the chosen real scalar in the coefficients. That value is not asserted here. -/
def current (i : Axis) (U : Config G n) (A : Directions G n) (x : Site n) :=
    aperture G i (sensor U A x)



/-- Literal clover with the curvature of the loop. -/
def clover (i j : Axis) (U : Config G n) (x : Site n) :=
  aperture G i fun a => aperture G j fun b => G.curvature (travel U x (Lattice.oriented a b))



/-- Stack the centered differences. -/
def stack (U : Config G n) (f : Site n → G.Color) : List Axis → Site n → G.Color
  | [] => f
  | i :: v => centered U (stack U f v) i

def stackSign (s : Signed) : List Axis → ℝ
  | [] => 1
  | i :: l => stackSign s l * sign s i





/-- With final transports from the chosen placement. -/
def landed (U : Config G n) (f : Site n → G.Color) (l : List Axis) (w : Walk) (x : Site n) :=
  G.adjoint (travel U x w) (stack U f l (stop x w))




end YM.ProjectorNext.Equivariance.Stencil
