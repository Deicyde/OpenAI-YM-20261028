import YM.R2I.Campaign.Clock

/-!
# An actual numerical bill chosen after block lengths

The numerical function may already depend on the selected block lengths.
This receipt is bought at every stage of the same Levels, and survives every
later DelayLe. It adds no assumption about a pre-existing Run.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativePostLengthPayment
open Lattice RG RG.Supply Push.PriceCompiler
open PhysicalNext.Repeat.Legato.R2I

variable {G : Gauge}

/-- The exact bill at the original first-stage profile index. -/
def StagePaid (F : ℕ → ℝ) (A : Levels G) : Prop :=
  ∀ m, F (A.clock.J (m + 1)) ≤ A.clock.hatBeta m

/-- Raising only the original beta-entry delay pays the entire fixed bill,
including stage zero, on every later compatible realization. -/
theorem eventuallyPaid (F : ℕ → ℝ) :
    EventuallyPaid (StagePaid (G := G) F) := by
  intro s P θ V
  let X : Delays θ :=
    { V with betaEntry := fun j => max (V.betaEntry j) (F j) }
  refine ⟨X, ⟨?_, le_rfl, le_rfl, le_rfl⟩, ?_⟩
  · intro j
    exact le_max_left _ _
  intro D hD B J A hA m
  exact (le_max_right (V.betaEntry (A.clock.J (m + 1))) _).trans
    ((hD.beta (A.clock.J (m + 1))).trans (hA.pays m))

end YM.Integration.NativePostLengthPayment
end
