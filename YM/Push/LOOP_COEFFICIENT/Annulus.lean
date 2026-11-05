import YM.Push.LOOP_COEFFICIENT.ContinuumTrace
import YM.Push.LOOP_COEFFICIENT.Crown

/-!
# Annular error and normalization
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Complex Matrix Lattice Laurent Bloch MeasureTheory Measure Filter Metric Set
open scoped Topology ContDiff BigOperators ENNReal InnerProductSpace
variable {G : Gauge} {a b μ C : ℝ} {f : E4 → ℂ}

def relativeScale (μ r : ℝ) := r + μ^2/r^2







structure Accuracy (f : E4 → ℂ) (G : Gauge) (a b μ C : ℝ) : Prop where
  inside k : ‖k‖ ≤ a*μ → ‖f k‖ ≤ C / μ^4
  middle k : k ∈ crown (a*μ) b → ‖f k - (annular G k:ℂ)‖ ≤ C * (relativeScale μ ‖k‖ / ‖k‖^4)
  outside k : k ∈ zone → b < ‖k‖ → ‖f k‖ ≤ C



namespace Accuracy
variable (h : Accuracy f G a b μ C) (ha : 0 < a) (hμ : 0 < μ) (he : a * μ ≤ b) (hb : b < Real.pi) (hC : 0 ≤ C)
    (hf : IntegrableOn f zone)
include h ha hμ he hb hC hf



end Accuracy


end YM.Push.Loops
