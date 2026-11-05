import YM.Progress.CLASSICAL_KIN_RECURSION.Blades

set_option warningAsError false

/-!
# Contractions. Independent = `kick (i,a)` in its own leg; dependent = separate
vector of signed shifts, defined later. `body` describes the exterior type of a
slot, enforced as zeros on off-grade inputs. Use even above top grade.
-/
set_option autoImplicit false
noncomputable section
open Filter Function
namespace YM.Progress.ClassicalKin.Spools
open Lattice RG Laurent Exterior
open scoped BigOperators Topology
variable {J X : Type} [Fintype J] [NormedAddCommGroup X] [NormedSpace ℝ X]

def Body (i : J) (r : ℕ) (u : Deck J X) : Prop := ∀ S, (S i).card≠r → u S=0






variable [DecidableEq J]






variable (i j : J) (p q : Axis → Shift (J × Axis))

def piece (a : Axis) : WorkDeck J X := (behind (hitch (p a))).comp (lower i a)
def δ : WorkDeck J X := ∑ a, piece i p a




omit [DecidableEq J] in
lemma exchange_behind (u : Deck J X) (x y) : behind (hitch x) (behind (hitch y) u)=behind (hitch y) (behind (hitch x) u) := funext fun _ => hitch_comm _ _ _





variable {i j}
omit [DecidableEq J] in
lemma Body.sum {u : Axis → Deck J X} {r : ℕ} (h : ∀ a, Body i r (u a)) : Body i r (∑ a,u a) := by
  intro S hs; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun a _ => h a S hs



end YM.Progress.ClassicalKin.Spools
