import YM.Progress.CLASSICAL_KIN_RECURSION.Bands

set_option warningAsError false

/-!
# Momentum-constrained lift to curvature legs n≥3, charged on the
universal cover. Includes origin. Extra displayed momentum variable
for the pin i is inert (kernels supported at 0 exponent there). It is
just a way to keep uniform Cauchy and position norm in the answer.
Reality builds in via `Reel`. Caller may take X *literally the space of
invariant color tensors*; no ambiguous averaging of a different gauge copy.
Does not price a numerical T which has yet to be estimated. Arity n=2 does not
use this result (ambiguity & low momentum hypotheses are different).
-/
set_option autoImplicit false
noncomputable section
open Filter Function
namespace YM.Progress.ClassicalKin.Spools
open Lattice RG Laurent Exterior
open scoped BigOperators Topology
variable {J X : Type} [Fintype J] [DecidableEq J] [NormedAddCommGroup X] [NormedSpace ℝ X]



variable (i : J)

/-- enforce inert coordinate in returned decks -/
def shoe (x : Shift (J×Axis)) : Cover := fun a => x (i,a)

def blazing (u : On (J×Axis) X) : On (J×Axis) X := fun b => if shoe i b=0 then u b else 0
omit [DecidableEq J] [NormedSpace ℝ X] in
lemma Drops.blazing {M σ : ℝ} {u : On (J×Axis) X} (h : Drops σ M u) : Drops σ M (blazing i u) := by
  intro x; unfold Spools.blazing; split
  · exact h x
  rw [norm_zero]; exact (norm_nonneg _).trans (h x)

def bolt : Reel (J×Axis) X →ₗ[ℝ] Reel (J×Axis) X where
  toFun u := ⟨blazing i u.val,by obtain ⟨σ,M,h,g⟩:= u.life; exact ⟨σ,M,h,g.blazing _⟩⟩
  map_add' a b := by apply Subtype.ext; funext x; change blazing i (a.val+b.val) x=blazing i a.val x+blazing i b.val x; unfold blazing; split; rfl; rw [add_zero]
  map_smul' a b := by apply Subtype.ext; funext x; change blazing i (a • b.val) x=a • blazing i b.val x; unfold blazing; split; rfl; rw [smul_zero]

def stuck := (behind (bolt i) : WorkDeck J X)
omit [DecidableEq J] in
lemma stuck_pay : Bus (stuck i : WorkDeck J X) := fun σ h => ⟨σ,1,h,one_pos,fun u M he S => by rw [one_mul]; exact (he S).blazing i⟩
omit [DecidableEq J] in
lemma stuck_with (u : Deck J X) : stuck i (stuck i u)=stuck i u := by
  funext S; apply Subtype.ext; funext x; change blazing _ (blazing _ _ ) x = blazing _ _ x; unfold blazing; split <;> rfl



variable [CompleteSpace X]














end YM.Progress.ClassicalKin.Spools
