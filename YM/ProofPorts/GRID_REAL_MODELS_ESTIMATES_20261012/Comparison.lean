import YM.Next.UV_STRESS.Influence
import YM.Next.UV_STRESS.Rates
import YM.Push.GRID_APPROXIMATION.Iterate



/-!
# Compare the actual grid-stop and phase-coarse error ports

Relate the true *random variables* in both APIs. This allows either
upstream estimate to feed the construction of the reflection models, with the
same physical support budget (`GridApprox.grows` etc.). We always use the
exact `Family`, not a family re-started at the coarse depth. Root at the link
cells of the GRID (full h-system, not a fixed size subset).

For `retrieve`, conditionally on the fine configuration, each negative OLD
copy is a constant. The positive NEW factors on the k-torus must still be
processed in the *same* conditional expectation! To move the product sign
out we will really have the disjoint cones, using `backTo_cells` (in
particular its implementation handles the shared tags). No claim that
unconditional expectations on these cells factorize.

Compare .

This does not itself
establish the physical attenuation estimate .

It identifies the
output to estimate and carries estimates through it, never via continuum
point passage or a product of single-source estimates.
-/

set_option autoImplicit false
noncomputable section

namespace YM.ProofPorts.GridRealModelsEstimates20261012

open RG Lattice Wilson Cells Filter MeasureTheory
open Push.GridApprox Next.UVStress
open scoped Topology BigOperators

lemma region_eq_window (n : Side) (r : ℕ) : region n r = window (0 : Site n) r := by
  simp [region, window]

variable {G : Gauge} (C : Family G)
variable {k m h N p r : ℕ}















lemma origin_local {U : Config G (C.side k p) → ℂ} (t : h ≤ k) (hk : k ≤ N)
    (hU : Interior (region (C.side k p) r) U) :
    Interior (window 0 (Push.GridApprox.grows C.path.levels k r hk)) (backTo C.path N p hk U) := by
  rw [region_eq_window] at hU
  rw [← show anchor C.S p (t.trans hk) 0 = 0 from (C.S.toDepth (t.trans hk) p).root.map_zero]
  apply backTo_local C.path N p t hk 0 r
  rw [show anchor C.S p t 0 = 0 from (C.S.toDepth t p).root.map_zero]
  exact hU

lemma origin_fits (p : ℕ) (t : h ≤ k) (hk : k ≤ N) (hroom : room C.path.levels h k r) :
    window 0 (Push.GridApprox.grows C.path.levels k r hk) ⊆ (tilesAt C.S p (t.trans hk)).chamber 0 := by
  have he := room_fits p C.path.levels r t hk hroom 0
  rw [show anchor C.S p (t.trans hk) 0 = 0 from (C.S.toDepth (t.trans hk) p).root.map_zero] at he
  exact he

variable {C}



end YM.ProofPorts.GridRealModelsEstimates20261012
