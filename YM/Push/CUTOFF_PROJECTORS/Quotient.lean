import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Work.A15

/-!
# A further real/H quotient check

Small subtlety: if comparing ranks via these projections,
`Aligned` only gives real H identification of the **kernel**, not of its
complement. Prove the quotient identification, *conditional* on getting
the aligned kernel. Use only the finite coordinates. Do not assume the
free Wick detector claim either - make its need explicit if asking for
Euclid/Comparator's `Ranks`. In particular nothing downstream licenses
pulling back an O(4) action by some ad hoc extension of these maps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.CutoffProjectors
open Function Filter Extraction Next.Extract Dash Labels
open scoped Topology BigOperators
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {C : Family G}





section Escape
-- A Schur-complement trick: make the upper block invertible as well as
-- the whole matrix, by avoiding finitely many eigenvalues. Works over
-- the real scalars (choose real t even though matrices here are complex).
variable {V Y : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]

omit [FiniteDimensional ℂ V] in
private lemma no_one_eigen (L : V →ₗ[ℂ] V) (μ : ℂ) (h : ¬ Module.End.HasEigenvalue L μ) :
    ∀ x, L x = μ • x → x = 0 := by
  intro x hx
  have h0 : Module.End.eigenspace L μ = ⊥ := not_ne_iff.mp (Module.End.hasEigenvalue_iff.not.mp h)
  have he := Module.End.mem_eigenspace_iff.mpr hx
  rw [h0] at he; exact he


end Escape







lemma free_null {F : Frames G} (d : ℕ) (h : Maxwell.residual G d = ⊥) :
    equationSpace (F.level d) = (Maxwell.freeTable F).null d := by
  ext x
  apply Iff.trans _ (Maxwell.projectionExact F)
  rw [equation_iff,h,Submodule.mem_bot, ← Maxwell.ideal_meaning]
  change Maxwell.observable G d ((F.level d).coords.symm x) = 0 ↔ Maxwell.snap F d x = 0
  exact ⟨fun hx => Subtype.ext hx, fun hx => congr_arg Subtype.val hx⟩


end YM.Push.CutoffProjectors
