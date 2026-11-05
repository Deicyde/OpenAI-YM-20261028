import YM.Integration.WilsonInverseCoadmission
import YM.Integration.WilsonInversePurchase

/-! The complete Calendar treasury is fixed from the original kernel before
the block lengths are chosen. Its nonzero preconditions are paid by a real
floor on those lengths; its running costs and the inverse cost are then paid
on the same later delays. The Names and dictionaries are never reselected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CalendarTreasuryPurchase

open Function Filter RG RG.Supply RG08 RG08.Admission Push.PriceCompiler
open Next.Foundations WilsonInverseSchedule
open scoped Classical Topology

variable {G : Gauge}

structure Plan (G : Gauge) (K : KernelChoices) where
  names : Names G K
  dialect (a : Ask) : Dialect (hol G) (localSection G) names a

def Plan.demands {K : KernelChoices} (P : Plan G K) (a : Ask) : Need :=
  treasury (chart G) (P.dialect a)

def Plan.floor {K : KernelChoices} (P : Plan G K) : ℕ → ℕ :=
  prePay P.demands

theorem plan_exists (hG : G.Simple) (K : KernelChoices) : Nonempty (Plan G K) := by
  obtain ⟨N⟩ := RG08.Admission.names hG K
  exact ⟨⟨N, fun a => Classical.choice
    (wishes (Next.Foundations.sound G) (valuation G) N a)⟩⟩

/-- One kernel-bound plan pays every fixed Ask on its admitted tail and
the inverse charge from level zero. -/
def TreasuryFunded (a : Levels G) : Prop :=
  ∃ P : Plan G a.clock.kernel,
    (∀ k n, Encodable.encode k ≤ a.clock.J n → Affords (P.demands k) a n) ∧
      Affords (inverseNeed P.names) a 0

/-- This is a post-length supplier only after the actual nonzero floor
has been purchased. Its conclusion is robust under every later delay. -/
theorem buy {s : Sheet G} {L : Rolls s} {θ : Protection L}
    (P : Plan G s.kernel) (hFloor : ∀ i, P.floor i ≤ (L.L i).val)
    (U : Delays θ) :
    ∃ V : Delays θ, DelayLe U V ∧
      ∀ (Z : Delays θ), DelayLe V Z →
        ∀ (B : Bar Z) (W : Wait B) (a : Levels G),
          Paid W a → TreasuryFunded a := by
  obtain ⟨V, hV, hPaid⟩ := minDelay P.demands hFloor U
  obtain ⟨X, hX, hInverse⟩ :=
    zeroPreDelay (inverseNeed P.names) (fun _ => rfl) V
  refine ⟨X, hV.trans hX, fun Z hZ B W a ha => ?_⟩
  have transported : ∃ Q : Plan G a.clock.kernel,
      (∀ k, Q.demands k = P.demands k) ∧
        inverseNeed Q.names = inverseNeed P.names := by
    rw [ha.kernel]
    exact ⟨P, fun _ => rfl, rfl⟩
  obtain ⟨Q, hQ, hQI⟩ := transported
  refine ⟨Q, ?_, ?_⟩
  · intro k n hn
    rw [hQ k]
    exact hPaid Z B W a (hX.trans hZ) ha k n hn
  · rw [hQI]
    exact hInverse Z B W a hZ ha

end YM.Integration.CalendarTreasuryPurchase
