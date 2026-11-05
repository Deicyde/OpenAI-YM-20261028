import YM.AnalyticNext.CUBIC_MATCH.Region.Kinetic
import YM.Progress.JOINT_CALENDAR.Issue



set_option warningAsError false

/-!
# Sum the cubic atoms and physical placements

The part of  concerning all main terms. Budget is
`O(1 + R3/L²)`, compatibility on entire tori -- cost independent of input
swell/width when measured as stated. Price only usable from sufficiently
large L (`θ/L ≤ σ` for transporting W.cubic). Top Wilson energy is `energy`
once, no orientation assumption at reading. For kinetic and cubic jointly,
channels with actual origins `dial` and the same Signed on terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid Work.F03
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {μ : Type*} {L : Side} {c f : μ → Side} {A B C D θ σ δ Λ : ℝ}
  {r : ShiftRoot c f} {V : ∀ p, Dir G (c p) → Dir G (f p)} {W : PathData G} {b : Clip}
section leg
variable (h : ScaleRead c f L r V θ C) {u : Cover} (hu : ofCell u L) (he : θ*tilt L ≤ σ)

include h hu he




end leg







section sums




end sums

/-- Use channels with explicit debit, don't split symmetrized field components. -/
def shaped (G : Gauge) (C δ θ B m : ℝ) := (Fintype.card PlaqAxes:ℝ)*squareFee G (C*Real.exp (θ*2)) θ δ B m

def pathSurcharge (θ C : ℝ) := slotOne (C*Real.exp (θ*2)) θ ^ 3







/-- actual Wilson read; top c=n. May use also under scale substitutions. -/
def summitFee (G : Gauge) (C θ : ℝ) := (Fintype.card PlaqAxes:ℝ)*(G.colorScale^2)⁻¹*shortOne G C θ*shortTwo G C θ


end YM.CubicMatch
