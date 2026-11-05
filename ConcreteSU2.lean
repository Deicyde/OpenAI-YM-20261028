import Solution
import YM.Examples.SU2

set_option autoImplicit false
noncomputable section
namespace YangMills
/-- The defining complex two-dimensional representation of SU(2). -/
def su2 : GaugeGroup :=
  let G := YM.Next.Foundations.SUtwo
  ⟨G.n,G.imageGroup,G.closed_imageGroup,G.lie,fun _ => Iff.rfl⟩

theorem su2Simple : su2.IsSimple := YM.Examples.SU2.simple

/-- Concrete specialization of the public challenge. -/
theorem su2Theory : ∃ C : WilsonFamily su2, WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) :=
  jointExistence su2 su2Simple
end YangMills
