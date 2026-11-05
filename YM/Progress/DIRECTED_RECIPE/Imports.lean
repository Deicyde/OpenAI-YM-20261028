import YM.Progress.DIRECTED_RECIPE.Marks
import YM.Progress.DIRECTED_RECIPE.Recipe
import YM.Progress.DIRECTED_RECIPE.Samples


/-!
# Importing coherent marker transfers

Works even when charged in a vocabulary first augmented after the
fact. Suppose the physics estimates and identities are on such an augmentation
(where still using EXACTLY these paths and the same history data, padding
only vacant terms). Pay the return on the original representation,
*without* new funding–and-history assumptions, using the dormant slots
proven there and the index-preserving readdressing. Never transform all
coefficients weightwise without checking it across all, including the unit.
Poly entries and full signal before expectation. Producers must still supply
real marker transfers--including applicability of same tuned label genealogy,
not assuming that the aligned-data hypothesis here holds automatically. E.g.
if external callers already occupied `sleepK`, renaming only the extra
calculations and then assuming they coincide with an unrenamed singleton
calculation would be wrong. See usage `Fired.pantry`. Recall ,
format . This file doesn't estimate the fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG Wilson Lattice Source Overlay Marker RG.Shoot
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {a : Levels G}

abbrev Branches (a : Levels G) := ℕ → ∀ p, Trail a p

/-- Readdressing pops cut out together over specific scales r..N, any
particular p. E.g. augment all supports for a source calculation,
then push BACK embeddings here (old to new isn't enough). -/
structure Aligned (e k : ℕ → ℕ ↪ ℕ) (A B : Branches a) (N p r : ℕ) : Prop where
  maps m : r≤m → m≤N → OverlayMap (e m) (k m) (A N p m) (B N p m)

namespace Aligned
variable {e k : ℕ → ℕ ↪ ℕ} {A B : Branches a} {N p r : ℕ} (h : Aligned e k A B N p r)

section linear
variable {d : ℕ} {F : Labels.Frame G d}

def take (k : ℕ → ℕ ↪ ℕ) (T : TransferData F ⟨a,A⟩ N p) (B : Branches a) : TransferData F ⟨a,B⟩ N p where
  entries m v := OverlayMap.relay (k m) (T.entries m v)
  terminal := T.terminal


end linear

section Many
variable {V : Type*} [Fintype V] [DecidableEq V] {R : Census V} (L : Lane (V:=V) ⟨a,A⟩ R N p)

def travel (k : ℕ → ℕ ↪ ℕ) (L : Lane ⟨a,A⟩ R N p) (B : Branches a) : Lane ⟨a,B⟩ R N p where
  sites m := OverlayMap.issue (k m) (L.sites m) (B N p m)
  load := L.load
  uses := L.uses

include h



end Many
end Aligned

/-- A computation in augmented dictionaries, over *one and the same*
trajectory's entries, with these embeddings on the indicated calls. Does not
alter any of the old labelled coefficient functions. -/
structure Augmented (e k : ℕ → ℕ ↪ ℕ) (A B : Branches a) (N p r : ℕ) : Prop extends Aligned e k A B N p r where
  fixed m : r ≤ m → m ≤ N → ∀ i, (B N p m).activities.forced (k m i) = (A N p m).activities.forced i

open Precision Next.Scheduling RG.Supply

variable {M : Horizon a} {O : ChartRatio G}
    {k : Kin M O} {r : Permissions a} {e : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage}


end YM.Progress.DirectedRecipe
