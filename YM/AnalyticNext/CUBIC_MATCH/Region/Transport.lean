import YM.AnalyticNext.CUBIC_MATCH.Region.WalkCost

set_option warningAsError false

/-!
# Actual paying of the Slot atSite

Hold offset anchor pre-cell (all residues will read at ≤4L). Account for
matrix transport across the placed curve, inverse to the same reference,
using curvature of **closed** transport. The naive charge on the long walks
can be used on its cross with curvature, but cannot be used on curvature's
first order itself. This enables kinetic and ℓ placement with no cubic or
future quartic reserve except that `Bounds` required analytically. ℓ uses
a genuine stronger row budget of its own, stated next, incl transport
length and independent of cubic cap; available via Joint.scribe (need more than the comparison with the stage
path cap alone here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid Work.F03
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {μ : Type*} {L : Side} {c f : μ → Side} {A B C D θ η σ : ℝ}
  {r : ShiftRoot c f} {V : ∀ p, Dir G (c p) → Dir G (f p)}
section comp



/-- Linear physical curvature of the matrix. -/
def hue (G : Gauge) : G.Mat →L[ℝ] G.Color := G.projectColor.toContinuousLinearMap ∘L
    ((1/2:ℝ) • (ContinuousLinearMap.id ℝ G.Mat-LocalRep.mirror G))







end comp

/-- Account a v inside the next period cell. Post operations will sum L^4. -/
def ofCell (u : Cover) (L : Side) := size u ≤ 4*L.val




def shortOne (G : Gauge) (C θ : ℝ) := faceFirst G C * Real.exp (θ*4)
def shortTwo (G : Gauge) (C θ : ℝ) := faceSecond G C θ * Real.exp (θ*4)^2





def slotOne (C θ : ℝ) := 2*C*Real.exp (θ*4)



/-- Long walk angle. Keep explicit price of length * tilt. -/
def travelOne (G : Gauge) (C θ : ℝ) := tileFee G C*Real.exp (θ*4)



/-- combine path and curvature. Include easy integer height factor, for
 later exponent buy. -/
def slotTwo (G : Gauge) (C θ : ℝ) := G.colorScale⁻¹*(shortTwo G C θ+2*travelOne G C θ*shortOne G C θ)


end YM.CubicMatch
