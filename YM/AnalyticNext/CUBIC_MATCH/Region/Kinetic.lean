import YM.AnalyticNext.CUBIC_MATCH.Region.Transport

set_option warningAsError false

/-!
# Pay the kinetic-face and row trials

Existence (if paying stipulated retained constants) of a FULL cover sum at
width with room for growth. Rate θ may be reduced before any of these estimates
are invoked. Useful even when widths after lift are much narrower: handled by
cost before L/`loads`, not hoping for iterated shrinking down an arbitrary
M(n). Uses ALL path legs, moment charge at fixed positive exponent, shared
row under `scribe`. These are unnormalized translation sums of coefficient
expressions, not activities or small-field product bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid Work.F03
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {μ : Type*} {L : Side} {c f : μ → Side} {A B C D θ δ σ Λ : ℝ}
  {r : ShiftRoot c f} {V : ∀ p, Dir G (c p) → Dir G (f p)} {W : PathData G} {b : Clip}












/-- shape quotation per face. Only direct (fixed via Strip/Floor), no
relaxation parameter. -/
def squareFee (G : Gauge) (C θ δ B m : ℝ) := m * (G.colorScale^2)⁻¹ * shortOne G C θ * shortTwo G C θ +
    (slotOne C θ*B) * (slotTwo G C θ*(1+2/δ)*B)











end YM.CubicMatch
