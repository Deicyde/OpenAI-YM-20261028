import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.AnalyticNext.QUARTIC_MATCH.Exchange
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.F05.Graphs



/-!
# Slice prescription for a funded scene

The full action including V-penalty, actual minimizing branch, tree and tag, REAL jets at 0.
Keep even the mixed and harmonic inputs. This file computes the jet to be matched,
not the output PathData construction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Filter Function Matrix Precision RG Lattice Exterior Tree Bid Work.F05 Tensor
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge}

namespace SliceExchange
variable {c f : Side} {S : StepData c f} {B : Forest S.ratio} {W : PathData G}
    {p : Clip} {b : Dir G c → AxisChart G B} (t : S.Choices)

/-- A real `Critical` on that tree is enough. -/
theorem on_shell (h : Critical B p W b) : OnShell (uncurry (tested B t p W)) b 0 := by
  obtain ⟨hf,he⟩ := h.2.2 t
  refine ⟨?_, h.2.1, ?_⟩
  · filter_upwards [he, (crit_home h).eventually (hf.eventually (by simp))] with x hx hv
    exact (Work.F04.hasFDerivAt_slice (uncurry (tested B t p W)) x (b x)
      (hv.differentiableAt (by simp))).unique hx
  rw [show arc b 0=0 from Prod.ext rfl h.1]; exact hf



variable {η : ℝ} (h : Critical B p W b)
include h








end SliceExchange
end YM.AnalyticNext.QuarticMatch
