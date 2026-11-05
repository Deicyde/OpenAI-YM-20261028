import YM.Exterior.Blade
import YM.Progress.CLASSICAL_KIN_RECURSION.Tape


set_option warningAsError false

/-!
# One Koszul argument at a time. Homological degree is supplied as a
predicate, so grade 0 and unused arguments take exactly the same operations
as the other grades. The contractions are in the scalar Laurent convention
(B tested at its own physical argument, not Hermitian-starred).
-/
set_option autoImplicit false
noncomputable section
open Filter Function
namespace YM.Progress.ClassicalKin.Spools
open Lattice RG Laurent Exterior
open scoped BigOperators Topology
variable {J X : Type} [Fintype J] [DecidableEq J] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (J X) in
abbrev Deck := (J → Finset Axis) → Reel (J × Axis) X
variable (J X) in
abbrev WorkDeck := Deck J X →ₗ[ℝ] Deck J X

/-- Lowering removes the contracted axis from the *input* blade.
Here S denotes the resulting blade. -/
def lower (i : J) (a : Axis) : WorkDeck J X where
  toFun u S := if a∈S i then 0 else parity (S i) a ℝ • u (update S i (insert a (S i)))
  map_add' u v := by ext S x; split <;> simp [*]
  map_smul' t u := by
    funext S; by_cases he:a∈S i <;> simp only [he,if_false,if_true,RingHom.id_apply,Pi.smul_apply,smul_zero]; rw [smul_comm]

def raise (i : J) (a : Axis) : WorkDeck J X where
  toFun u S := if a∈S i then parity (S i) a ℝ • u (update S i ((S i).erase a)) else 0
  map_add' u v := by ext S x; split <;> simp [*]
  map_smul' t u := by
    funext S; by_cases he:a∈S i <;> simp only [he,if_false,if_true,RingHom.id_apply,Pi.smul_apply,smul_zero]; rw [smul_comm]

/-- per-symbol changes, no touching blade indices -/
def behind (f : Reel (J × Axis) X →ₗ[ℝ] Reel (J × Axis) X) : WorkDeck J X where
  toFun u S:= f (u S)
  map_add' u v := by funext S; exact f.map_add _ _
  map_smul' t u := by funext S; exact f.map_smul _ _

@[simp] lemma run_lower (u : Deck J X) (i a S) : lower i a u S = if a∈S i then 0 else
    parity (S i) a ℝ • u (update S i (insert a (S i))) := rfl
@[simp] lemma run_raise (u : Deck J X) (i a S) : raise i a u S = if a∈S i then
    parity (S i) a ℝ • u (update S i ((S i).erase a)) else 0 := rfl
omit [DecidableEq J] in
@[simp] lemma run_behind (u : Deck J X) (f S) : behind f u S=f (u S) := rfl



















end YM.Progress.ClassicalKin.Spools
