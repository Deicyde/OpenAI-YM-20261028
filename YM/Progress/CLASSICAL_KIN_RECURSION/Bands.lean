import YM.Progress.CLASSICAL_KIN_RECURSION.Blades

set_option warningAsError false

/-!
# Algebraic charges on decks, grounding symbols by universal kernel
estimates (not periods). Every composition request answered *for any*
input width, then issues a new positive width & ceiling, never
forecasting from the particular realized kernels.
-/
set_option autoImplicit false
noncomputable section
open Filter Function
namespace YM.Progress.ClassicalKin.Spools
open Lattice RG Laurent Exterior
open scoped BigOperators Topology

variable {J X : Type} [Fintype J] [NormedAddCommGroup X] [NormedSpace ℝ X]

def Credit (σ M : ℝ) (u : Deck J X) := ∀ S, Drops σ M (u S).val

def Bus (f : WorkDeck J X) := ∀ σ : ℝ,0<σ → ∃ w K : ℝ,0<w ∧ 0<K ∧
    ∀ u : Deck J X, ∀ M, Credit σ M u → Credit w (K*M) (f u)













variable [DecidableEq J]





end YM.Progress.ClassicalKin.Spools
