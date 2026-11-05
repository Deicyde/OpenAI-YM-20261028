import YM.Analysis.Polydisc
import YM.Progress.CLASSICAL_KIN_RECURSION.Along


set_option warningAsError false

/-!
# Auxiliary docks for the same patch and block law. Over itself,
include translations. All winding slots queried before shrinking.
`weight/worth` counts actually multiplied into the test cost, not new
cover choices.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Tent
open Lattice RG Exterior Wilson Precision Tree Bid Bloch Laurent
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n m : Side}

abbrev below (P : Patch) (n : Side):Side:=n*P.L
def dock (P : Patch) (K : KernelChoices) (n : Side): StepData n (below P n):= ⟨P,K,rfl⟩
abbrev shores (P : Patch) (n : Side):Ratio n (below P n):= ⟨P.L,rfl⟩

section little
variable (h : divides n m)


def lieBy (p : Site n) (x : Site m):= shrinkTo h x+p






end little

lemma shrinks_self (n : Side) (x : Site n): shrinkTo (n:=n) (dvd_refl _) x=x:=by
  have hh:=shrinkWrap (n:=n) (dvd_refl _) (lift x); simp only [wrap_lift] at hh; exact hh
lemma lies_self (n : Side) (p x : Site n):lieBy (dvd_refl _) p x=x+p:=by unfold lieBy; rw [shrinks_self n]


section both
variable (h : divides n m) (p : Site n) (P : Patch)
include h in
lemma also : divides (below P n) (below P m):=mul_dvd_mul_right h P.L.val













end both
end YM.Progress.ClassicalKin.Tent
