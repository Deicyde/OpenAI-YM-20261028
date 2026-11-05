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
import YM.Pressure.Rows
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15
import YM.Work.B06


set_option warningAsError false

/-! # Through the normalized tags – `lift` & `farther` invocation

Differentiation currency is order k only. Sufficient actual
conditional-kernel estimates are on parameters FIN(l) of left increment
(V may be boundary, hence germ must be defined also outside g_Y).
Doesn't interchange k+1 estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Quartet
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source  Analysis
   
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)

abbrev Winds (i : ℕ) := Fin i → ℝ



def playing : (l : List (Directions G n)) → Config G n → Winds l.length → Config G n
  | [],U,_ => U
  | x :: l,U,t => playing l (increment U (t 0 • x)) (Fin.tail t)











/-- One domination at finite regulator. Neighborhood can depend on family
and volume & out-V but *not* noise (tag, Z) points. Smooth data already patched
outside invoked region and handed to US as same measure and density factors.
Doesn't impose uniform estimates for denominators. Exact normalized probability
 and high moments at t=0 are a separate currency. -/
structure Amplitude (k i : ℕ) (U : Set (Winds i)) (B : Z → Winds i → ℂ) (p : Z→ℝ) : Prop where
  area : IsOpen U
  ticket : Integrable p μ
  hear : ∀ (m:ℕ),m ≤ k → ∀ x∈U,AEStronglyMeasurable (fun a => iteratedFDeriv ℝ m (B a) x) μ
  here : ∀ᵐ z∂μ, ∀ x∈U,ContDiffAt ℝ k (B z) x ∧ ∀ (m:ℕ),m ≤ k → ‖iteratedFDeriv ℝ m (B z) x‖ ≤ p z






end YM.MultiNext.SignedSource.Quartet
