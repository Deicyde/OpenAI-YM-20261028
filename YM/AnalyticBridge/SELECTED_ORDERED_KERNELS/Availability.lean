import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Grams
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Recenter

/-!
# Gap over the real no-hole open ball, alongside the forward precision bills

AFTER L. Estimate displacement explicitly in unweighted Schur via localized
first-order budgets and the real MVT; plain continuity on a configuration
space of torus-dependent dimension would not justify this radius. Do not
require covariance/same tags across periods or anything about a continuum
family. Keep *simultaneous* tag changes of the path-tail kernel too. Limits
below do not include a single inverse assumption. They are proven, not an
input from a separate task.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Small
open Lattice Wilson RG Precision Tree Exterior Function Filter Topology Bloch Laurent Metric Matrix FreeResolvent Affine
  Lifted View TestD Mark
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {P : Patch} {K : KernelChoices} {n k : ℕ} {S : StepData c f}
  {σ C M d η α V V' r : ℝ} {t : S.Choices} {B : Vec G c 1} {W : PathData G}

section qf
variable {ι : Type*} [Fintype ι] {F : Vec G c 1 → Matrix ι ι ℝ} {a : ι → Site c}



end qf

-- Use Gap directly on identity-completed family.
def tariff (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) := min ((headGap G P K p)/2) 1
lemma tariff_pos (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) : 0 < tariff G P K p := lt_min (half_pos (headGap_pos ..)) zero_lt_one

structure Limits (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (σ M : ℝ) (n k : ℕ) (r C : ℝ) : Prop where
  pos : 0 < r
  nonneg : 0 ≤ C
  safe {c : Side} (B : Vec G c 1) : ‖B‖ < r → ∀ i, ‖paint G c B i‖ < radius G k
  uniform {W : PathData G} {d : ℝ} : Sheet W σ M → 0 ≤ d → d ≤ tier σ n → ∀ {c f : Side} {h : f.val=c.val*P.L.val}, Bid.Larger (G:=G) (data h K) →
    ∀ (t : (data h K).Choices) (B : Vec G c 1), ‖B‖ < r → let S := data h K
    (∀ R : Admit, (∀ T : Forest S.ratio, Gap (primary S T t p W R B) (headGap G P K p / 2)) ∧
      Allow B n d (tier σ n) (squarePrice P G K p σ n C M) (home S) (home S) (block S t p W R)) ∧
    ∀ R : ℕ, Allow B n d (tier σ n) (tailPrice P G σ n R C M) (home S) (home S) (block S t p W all-block S t p W (shorter R))



end YM.SelectedOrderedKernels.Small
