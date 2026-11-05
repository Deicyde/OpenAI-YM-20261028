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
import YM.Work.A07
import YM.Work.B04
import YM.Work.B06

/-! Classical stress and leading balance under the unmasked radial-link test. No contacts
or products in the continuum are evaluated by this calculation. It checks the Wilson
price-part normalization (NOT convergence on Wilson expectations). Both divergence of the
vector field in link space and cutoff renormalizations must still be accounted for.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Function Gauge Labels Source Wilson Lattice RG
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {G : Gauge} {D : ℕ}
























private def threshold (m : ℕ) : ℝ := if m=5 then 120 else 0






end YM.StressFlux
