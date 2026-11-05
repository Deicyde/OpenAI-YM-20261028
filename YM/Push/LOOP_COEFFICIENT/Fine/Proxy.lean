import Mathlib.Analysis.Complex.Schwarz
import YM.Push.LOOP_COEFFICIENT.Fine.Operators

/-!
# Auxiliary flat vector fiber on the free strip (no input path width)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Fine
open Matrix Function Filter Set Metric Complex Lattice Laurent RG Wilson Precision Exterior Bloch Bid Kernel Continuum Paths
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {H : Precision.Bed} {W : PathData G} {p : Clip} {n : Side} {μ η r C D σ Λ u : ℝ} {k : Momentum} {a d : Type} [Fintype a] [DecidableEq a]

def proxy (G : Gauge) (H : Bed) (μ : ℝ) (k : Momentum) : Matrix (Axes G) (Axes G) ℂ := kineticSymbol G H.metric k + ((root G).mul (root G).transpose).base k + (surfeit G μ).base k


private lemma pow_base (V : Vertex d a a) (k : ℕ) (p : Momentum) : (V.pow k).base p = V.base p ^ k := by induction k <;> simp_all [Vertex.pow,Vertex.mul,Vertex.id,Vertex.const,pow_succ]
def ribbon (a : Type) [Fintype a] [DecidableEq a] (M : Matrix a a ℂ) (n : ℕ) := ∑ i∈Finset.range n,M ^ (i+1)
lemma upper_base (V : Vertex d a a) (k : ℕ) (p : Momentum) : (V.upper k).base p = ribbon a (V.base p) k := by induction k <;> simp_all [ribbon, Finset.sum_range_succ,Vertex.upper,Vertex.const,Vertex.add,pow_base]
def more (M : Matrix a a ℂ) := ribbon a M depth + (ribbon a M depth + ribbon a M depth*ribbon a M depth)
lemma excess_base (V : Vertex d a a) (p : Momentum) : V.excess.base p = more (V.base p) := by simp [more,Vertex.excess,Vertex.add,Vertex.mul, upper_base]



lemma factor_base (G : Gauge) (μ : ℝ) (k : Momentum) : (factor G μ).base k = ((μ^2:ℝ):ℂ) • ((gauged G μ).base k)⁻¹ := by simp [factor,Vertex.smul,Vertex.inv,Vertex.add,Vertex.inc,Vertex.neg,Vertex.mul,Vertex.const]
lemma massive_base (G : Gauge) (μ : ℝ) (k : Momentum) : (massive G μ).base k = ((μ^2:ℝ):ℂ) • ((onAxis G ((factor G μ).base k))^depth) := by simp [massive,Vertex.smul,pow_base,lift]
lemma surfeit_base (G : Gauge) (μ : ℝ) (k : Momentum) : (surfeit G μ).base k = longitudinal G k * more ((factor G μ).base k) * (longitudinal G (-k)).transpose + (massive G μ).base k := by simp [surfeit,Vertex.add,Vertex.mul,Vertex.transpose,root,excess_base]












def Windowed (k : Momentum) := star k=k ∧ ∀ i, |(k i).re|≤Real.pi
def ruler (μ : ℝ) (k : Momentum) := ‖k‖+μ


end YM.Push.Loops.Fine
