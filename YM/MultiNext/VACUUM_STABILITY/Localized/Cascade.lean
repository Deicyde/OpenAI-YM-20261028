import YM.MultiNext.VACUUM_STABILITY.FirstGas

set_option warningAsError false

/-!
# Restoring the stickers all at once or across cascading mergers

Check on PACK sums with their actual flags. In particular, the pipeline used at `Settled`
which merges stickers from normalization, extraction and forced exclusions together is
consistent with a computation using extra post-merging stages. This result is stronger than
just comparing total partition functions, which does not suffice for `Settled.floorK` or
fresh K receipts. Still need check choices and appearances of the actual families on the
upstream side, coefficient by coefficient when necessary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Windows
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {I J H : Type} {n : Side} (D : Hearth n I J)

-- New attaching terms triggering under actual flags
structure Recipes (n : Side) (H : Type) where
  zone : H → Support n
  hit j : (zone j).Nonempty















-- help was originally opaque `Choices` product



end YM.Multi.Vacuum.Windows
