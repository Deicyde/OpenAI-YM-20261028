import ChallengeSpec

set_option autoImplicit false
noncomputable section
namespace YangMills
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace Hierarchy
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
/-- A distribution on the full configuration space, including every collision diagonal,
whose restriction to pairwise separated insertions is the same correlation function. -/
def Contacts : Prop := ∀ (s : Option T.Character) (n : ℕ) (v : Fin n → T.Tag),
  ∃ D : _root_.TestFunction (⊤ : Opens (Points n)) ℂ ⊤ →L[ℂ] ℂ, ∀ f : _root_.TestFunction (⊤ : Opens (Points n)) ℂ ⊤,
    tsupport f ⊆ WilsonFamily.separated n → D f = ∫ x, f x * T.correlation s v x

end Hierarchy

end YangMills
