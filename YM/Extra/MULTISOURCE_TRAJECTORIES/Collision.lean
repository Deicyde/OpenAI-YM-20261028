import Mathlib.Analysis.Analytic.Binomial
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
import Mathlib.RingTheory.Nilpotent.Exp
import YM.Analysis.Polydisc
import YM.Work.A07
/-!
# A tempting shortcut is not an identity of blocking

Pointwise product of separately pushed normalized one-marker coefficients,
with only one vacuum, does *not* in general give the joint pushed coefficient.

Prove the strict collision test for every continuous real nonconstant cylinder,
in particular an actual Wilson plaquette in the chosen normalization and every
allowed nonabelian image.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open RG Wilson Lattice Function Filter MeasureTheory Marker Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {c f : Side} (S : StepData c f) (β : ℝ)





private lemma actual (h : G.Simple) : ∃ g : G.El, g ≠ 1 := by
  by_contra! he
  obtain ⟨X,hX,Y,-,hn⟩ := h.1
  have ha : ∀ t : ℝ, NormedSpace.exp (t • X) = (1 : G.Mat) := by
    intro t; obtain ⟨u,hu⟩ := G.mem_lie.mp hX t; rw [← hu,he u,G.mat_one]
  have hd := hasDerivAt_exp_smul_const X (0 : ℝ)
  have hd' : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X)) X 0 := by simpa using! hd
  rw [funext ha] at hd'
  have hv := hd'.unique (hasDerivAt_const ..)
  rw [hv] at hn; simp at hn




end YM.Extra.Trajectories
