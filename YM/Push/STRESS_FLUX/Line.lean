import YM.Push.STRESS_FLUX.Conserved

/-!
Uniqueness and conditioning of the centered conserved line,
excluding constants by a physical one-point constraint, no continuum T fixed
in advance. A real-H alignment at 4 and 5 on a single sufficient weak scheme
and the first-jet tests suffice. These are still not claimed here from birth
or Bare or any continuum subsequence alone. Complements Weak (normalization
can be *chosen*, on further subsequences, with sign coherent).
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Line
open Filter Set Function Table Climb
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {H : S.RealSpin} {A : (Bel L).RealSpin} {V : DiffPlan S}
  {n d m : ℕ} {R : ℝ}



def skim (H : S.RealSpin) := Complex.reCLM.toLinearMap ∘ₗ ((average S 0).restrictScalars ℝ) ∘ₗ (LinearMap.proj (R:=ℝ) (0:Axis)) ∘ₗ (LinearMap.proj (0:Axis)) ∘ₗ (TableTwo H).subtype

def closureMap (h : V.Orientation H) := (skim H).prod (rankOp V h)





private abbrev base := axisLine (basis 0)











end YM.StressFlux.Line
