import YM.Push.LOOP_COEFFICIENT.Block.Optimize

/-!
# One step all-period certificates under free-kernel and path hypotheses

The output Γ,γ (and slice gap) cost fixed block data, not depth, forest,
period, tags, Haar-ratio choice, input-loop cap or actual path choice. The
transported piece of the new loop cap, drift and width have the earlier
choice order in the statement. No `ρ` or model for a determinant is an
input in the coefficient calculation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Producer
open Matrix Set Filter Function Lattice Laurent RG Precision Wilson Exterior Bloch Bid Gauge Block Portal  Kernel Fine Tree
open scoped Topology BigOperators ContDiff
variable {c f L : Side} {P : Patch} {G : Gauge} {K : KernelChoices} {W U : PathData G} {p q : Clip} {O : ChartRatio G} {T : Towers P.L} {H H' : Bed} {ξ u A σ C Λ : ℝ}

abbrev Coherent {c f : Side} (P : Patch) (K : KernelChoices) (T : Towers P.L) (H H' : Bed) (h : f.val = c.val * P.L.val) := let S := StepData.mk P K h; Precision.Inputs S (installed S.ratio T.A0) (H.metric.acts f) (H'.metric.acts c)
structure Slides (P : Patch) (K : KernelChoices) (T : Towers P.L) (H H' : Bed) where
  co : ℕ → Side
  fine : ℕ → Side
  size i : (fine i).val = (co i).val * P.L.val
  grows : Expands co
  coherent i : Coherent P K T H H' (size i)
structure Every (P : Patch) (K : KernelChoices) (T : Towers P.L) (O : ChartRatio G) (p q : Clip) (W U : PathData G) (α η Γ γ Λ : ℝ) : Prop where
  vertical {c f : Side} (h : f.val=c.val*P.L.val) (F : Forest (StepData.mk P K h).ratio) : PriceGap F (S:=StepData.mk P K h) p W η
  existence {c f : Side} (h : f.val=c.val*P.L.val) (F : Forest (StepData.mk P K h).ratio) : ∃ ρ,Critical F (S:=StepData.mk P K h) p W ρ
  keeps {c f : Side} (h : f.val=c.val*P.L.val) (F : Forest (StepData.mk P K h).ratio) ρ : let S := StepData.mk P K h
    Critical F (S:=S) p W ρ → Guessed F (S:=S) (installed S.ratio T.A0) ρ → FiniteBound (S:=S) F W U p q α O ρ Γ γ Λ







end YM.Push.Loops.Producer
