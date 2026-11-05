import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Push.LOOP_COEFFICIENT.Grids
import YM.Push.LOOP_COEFFICIENT.LogKernel



/-!
# Combined orbital, spin and ghost on the transverse annular test

Momentum along axis 0; external A-waves both along axis 1, same physical
unit color polarization. Order is -p,p in the mixed second *field*
derivative. E_{il}=δ_{i1}δ_{l0}-δ_{i0}δ_{l1} (output first, for 2 ad F_{li}).
Counting real generators complexified in Fourier, unrestricted k, 1/2 and
-1 weights. Only divide momentum (not field) derivative by 2!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Complex Matrix Lattice Laurent Bloch Filter
open scoped Topology ContDiff BigOperators Kronecker Matrix.Norms.L2Operator InnerProductSpace
variable {G : Gauge} {b d : Type} [Fintype b] [DecidableEq b]

-- Exact slots used in one sampled trace.
structure Reading (b : Type) where
  plain : Matrix b b ℂ
  shift : Matrix b b ℂ
  forw : Matrix b b ℂ
  back : Matrix b b ℂ
  tad : Matrix b b ℂ

def Reading.eval (R : Reading b) := (R.plain * R.tad).trace - (R.plain * R.back * R.shift * R.forw).trace

def Reading.ofVertex (V : Vertex d b b) (q p : Momentum) (v : CSpace d) : Reading b where
  plain := (V.base q)⁻¹
  shift := (V.base (q+p))⁻¹
  back := V.one (q+p) (-p) v
  forw := V.one q p v
  tad := V.two q (-p) p v v

lemma Reading.exact (V : Vertex d b b) (q p : Momentum) (v : CSpace d) : (ofVertex V q p v).eval = bubbleTrace V v v p q := by rw [bubbleTrace,LogStrip.bubble_expr,Matrix.trace_sub]; rfl

def carrier (T : G.Color) : Matrix G.ColorIndex G.ColorIndex ℂ :=
  let b := EuclideanSpace.basisFun G.ColorIndex ℝ
  cmat ((LinearMap.toMatrix b.toBasis b.toBasis) (G.ad T))
def spinPlane : Matrix Axis Axis ℂ := Matrix.single 1 0 1 - Matrix.single 0 1 1






def disc (k : E4) (t : ℂ) := (‖k‖:ℂ)^2 + 2*t*(k 0:ℝ) + t^2

def scalarFlat (k : E4) (t : ℂ) (T : G.Color) : Reading G.ColorIndex where
  plain := (disc k 0)⁻¹ • 1
  shift := (disc k t)⁻¹ • 1
  forw := (-2 * I * (k 1:ℝ)) • carrier T
  back := (-2 * I * (k 1:ℝ)) • carrier T
  tad := (-2:ℂ) • (carrier T)^2

def vectorFlat (k : E4) (t : ℂ) (T : G.Color) : Reading (Axes G) where
  plain := (disc k 0)⁻¹ • 1
  shift := (disc k t)⁻¹ • 1
  forw := 1 ⊗ₖ (scalarFlat k t T).forw + (2 * I * t) • (spinPlane ⊗ₖ carrier T)
  back := 1 ⊗ₖ (scalarFlat k t T).back + (-2 * I * t) • (spinPlane ⊗ₖ carrier T)
  tad := 1 ⊗ₖ (scalarFlat k t T).tad









@[simp] lemma disc_zero (k : E4) : disc k 0 = (‖k‖:ℂ)^2 := by simp [disc]









/-- Annular degree-two coefficient before k integration. -/
def annular (G : Gauge) (k : E4) : ℝ := 4 * G.casimir * (k 1^2 / ‖k‖^6 - 4*(k 1^2*k 0^2 / ‖k‖^8) - 1/‖k‖^4)


end YM.Push.Loops
