import YM.Push.LOOP_COEFFICIENT.Fine.Quanta
import YM.Push.LOOP_COEFFICIENT.Fine.Tilt



/-!
# Margins at the three internal arguments of one reading
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Fine
open Function Set Filter Matrix Metric Lattice Laurent RG Wilson Precision Exterior Bloch Bid Continuum Paths Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {p : Clip} {H : Bed} {W : PathData G} {b : Type} [Fintype b] [DecidableEq b]
  {η C σ r e M μ D θ A χ δ : ℝ}

def ray (t : ℂ) := t • unitAxis 0

def crew (k : E4) (t : ℂ) : Set Momentum := {q | q = radians k ∨ q = radians k + ray t ∨ q = radians k + -(ray t)}
def duet (t : ℂ) : Set Momentum := {p | p = ray t ∨ p = -ray t}
@[simp] lemma ray_mem (t : ℂ) : ray t ∈ duet t := Or.inl rfl
@[simp] lemma nRay_mem (t : ℂ) : -(ray t) ∈ duet t := Or.inr rfl










structure Margin {d b : Type} [Fintype d] [Fintype b] [DecidableEq b] (X : Vertex d b b) (k : E4) (t : ℂ) (r e M : ℝ) : Prop where
  law : StripLaw X (crew k t) (duet t)
  cost : Quanta X (crew k t) (duet t) r (M*r^2)
  gap q : q ∈ crew k t → Gap (X.base q) (e*r^2)

/-- Sufficient actual flat and classical bounds, common parameters (no choice
of r,η or C over shell parameters here). -/
structure Reserve (W : PathData G) (p : Clip) (χ g η C : ℝ) : Prop where
  budget : ∃ σ D Λ, W.Bounds p σ D Λ
  packet : Packet (localVertex W p) η C
  floor : ∃ H : Bed, Holds G H χ g ∧ ∀ μ, 0<μ → μ≤1 → ∀ z∈Tube η, (complete W p μ).base z = proxy G H μ z

variable {g : ℝ}






end YM.Push.Loops.Fine
