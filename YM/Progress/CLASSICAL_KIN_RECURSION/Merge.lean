import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.Tannery
import YM.Progress.CLASSICAL_KIN_RECURSION.Blades

set_option warningAsError false

/-!
# Evaluating decks in typed scalar products (real). Physical site & type
multiplicities exactly, no restriction to collinear argument tests.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Spools
open Lattice RG Laurent Exterior
open scoped BigOperators Topology
variable {J α : Type} [Fintype J] [Fintype α] [DecidableEq J] {n : Side}

variable (J α) in
abbrev Tones := (J → α) → ℝ
variable (J α) in
abbrev Voices := Deck J (Tones J α)
variable (α) in
abbrev ToneTest (n : Side) := Finset Axis → Site n → α → ℝ

def sing (v : J → ToneTest α n) (S : J → Finset Axis) (p : J → Site n) (b : J → α) :=
    ∏ i, v i (S i) (p i) (b i)







def bead (i : J) (v : J → ToneTest α n) (S : J → Finset Axis) (p : J → Site n) (b : J → α) :=
    ∏ j ∈ Finset.univ.erase i, v j (S j) (p j) (b j)
omit [Fintype α] in
lemma sing_erase (i : J) (v : J → ToneTest α n) (S p b) : sing v S p b=bead i v S p b * v i (S i) (p i) (b i) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
omit [Fintype α] in
lemma bead_same (i : J) (v w : J → ToneTest α n) (S T : J → Finset Axis) (p q : J → Site n) (b : J → α)
    (h : ∀ j, j≠i → v j (S j) (p j) (b j)=w j (T j) (q j) (b j)) : bead i v S p b=bead i w T q b :=
    Finset.prod_congr rfl fun j hj => h j (Finset.mem_erase.mp hj).1
omit [Fintype α] in
lemma sing_update (i : J) (v : J → ToneTest α n) (W) (S p b) : sing (update v i W) S p b=bead i v S p b*W (S i) (p i) (b i) := by
  rw [sing_erase i,update_self]; congr 1; exact bead_same i _ _ _ _ _ _ b fun j hj => by rw [update_of_ne hj]



/-- Extend values to all grades; this discrete coboundary matches d
on individual grades in force. -/
def motion (a : Axis) (v : ToneTest α n) : ToneTest α n := fun S p f => if a∈S then
    parity S a ℝ * (v (S.erase a) (p+step a) f - v (S.erase a) p f) else 0
def advance (v : ToneTest α n) : ToneTest α n := ∑ a,motion a v


end YM.Progress.ClassicalKin.Spools
