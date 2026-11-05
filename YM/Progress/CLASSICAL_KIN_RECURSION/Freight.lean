import YM.Pressure.Seeds
import YM.Progress.CLASSICAL_KIN_RECURSION.Orchard

set_option warningAsError false

/-!
# Analytic product weights for all lists through a prescribed k
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Orchard
open Lattice RG Laurent Exterior Wilson Precision Tensor Analysis
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius

section packs
variable {A : Type*}

def pack (f : A→ℝ) (l : List A) := (l.map f).prod
@[simp] lemma pack_nil (f : A→ℝ) : pack f []=1:=rfl
@[simp] lemma pack_cons (f : A→ℝ) (a) (l) : pack f (a::l)=f a*pack f l:=rfl











end packs

section norms
variable {X Y Z T : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- Spray in *possibly crude* local size carrier `m`.
Stamp with powers e.g. `M=L⁻²` when applying with improved products on
flat; may have m(b) ≥ O(L) on the rough leg. -/
def Ship (F : X→Y) (p : X) (m : X→ℝ) (k : ℕ) (C : ℝ) : Prop := ∀ l : List X,l.length ≤ k → ‖spray F l p‖ ≤ C*pack m l


end norms
end YM.Progress.ClassicalKin.Orchard
