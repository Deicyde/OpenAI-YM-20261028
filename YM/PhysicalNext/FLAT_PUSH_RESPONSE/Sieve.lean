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
import YM.Ac.Table
import YM.Bid.Drops
import YM.Org.Theatre
import YM.Pressure.Seeds
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian
import YM.Work.A05.Read
import YM.Work.A07
/-!
# Differentiate with domination; some calculator tools

At finite parameters, prior to any large-beta arguments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open MeasureTheory Function Filter Metric Set Next.SectorChange.Gaussian
open scoped Topology BigOperators ContDiff ENNReal
variable (F : ℝ→ℝ)
def accel (x : ℝ) := deriv (deriv F) x

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Z : ℝ × E → ℝ} {u : ℝ × E}



section sieve
variable {X : Type} [MeasurableSpace X] {s : Set ℝ} {ν : Measure X} {B C : X → ℝ}
    {R Q P : ℝ → X → ℝ} {x : ℝ}

structure Sieve (R Q P : ℝ → X → ℝ) (s : Set ℝ) (ν : Measure X) (B C : X → ℝ) : Prop where
  top : ∀ t ∈ s, Integrable (R t) ν ∧ AEStronglyMeasurable (Q t) ν ∧ AEStronglyMeasurable (P t) ν
  coin : Integrable B ν ∧ Integrable C ν
  quotes : ∀ᵐ u ∂ν, ∀ t∈s,‖Q t u‖ ≤ B u ∧ ‖P t u‖ ≤ C u
  enter : ∀ᵐ u ∂ν, ∀ t∈s, HasDerivAt (fun x => R x u) (Q t u) t ∧ HasDerivAt (fun x => Q x u) (P t u) t


-- near input, noncircular


end sieve
variable {ι : Type} [Fintype ι] {I : Set (Vec ι)} {R : ℝ × Vec ι → ℝ} {t : Set ℝ}

-- Compact domains w/fixed truncation


-- isolate exp derivatives (pointwise). No mask motion here.
variable {r : ℝ} {x : ℝ} {f g : ℝ → ℝ}




end YM.PhysicalNext.FlatResponse
