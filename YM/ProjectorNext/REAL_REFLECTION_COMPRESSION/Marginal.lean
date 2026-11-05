import Mathlib.MeasureTheory.Integral.Pi


set_option warningAsError false
/-!
# Restricted read-set for product averaging

Probability densities relative to counting or to finite product Haar, all
arguments conditional. Use the identities for **integrable** entries; also
true for totalized integral versions here, but we do not infer integrability
from them. Needed at both tag and bond levels; bond distributions (conditional
on *all* site tags) can depend on those same tags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror.Marginal
open Set Filter Function MeasureTheory
open scoped Topology BigOperators
variable {I E : Type*}

/-- A function of a finite array uses only coordinates in X. -/
def Uses (X : Set I) (F : (I → E) → ℂ) := ∀ x y, EqOn x y X → F x = F y



section Both
variable [Fintype I]


end Both
section Split
variable (X : I → Prop) [DecidablePred X]
private abbrev In (X : I → Prop) (E : Type*) := Subtype X → E
private abbrev Out (X : I → Prop) (E : Type*) := { i // ¬ X i } → E
private def e := Equiv.piEquivPiSubtypeProd X (fun _ => E)

private lemma first {F : (I → E) → ℂ} (h : Uses {i|X i} F) (x : In X E) (y z : Out X E) :
    F ((e X).symm (x,y)) = F ((e X).symm (x,z)) := by
  apply h
  rintro i (hx : X i)
  simp only [e,Equiv.piEquivPiSubtypeProd_symm_apply,hx, ↓reduceDIte]


variable [Fintype I]

end Split

section Integral
variable [Fintype I] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]







variable [Nonempty E]




end Integral

section Counting
variable [Fintype I] [DecidableEq I] [Fintype E]






variable [Nonempty E]




end Counting
end YM.ProjectorNext.RMirror.Marginal
