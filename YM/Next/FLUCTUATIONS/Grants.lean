import YM.Integrated
import YM.Next.FLUCTUATIONS.Bare
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04
import YM.Work.B06


/-!
# RGrants: the pre and post pressure grant

No roll length/smoothing delay instantiated. Can use as an implication
in the pre-L ledger, then raise waits to pay this part after L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Lattice RG RG.Supply Wilson Pressure Precision Input
open scoped Topology BigOperators
variable {G : Gauge}

/-- Now requires no separate EBare input. Still a grant (universal
conditional price), not a realized S or trajectory. -/
theorem grants (P : Teller G) : Teller.Grants P := Integrated.pressure_grants bare P

theorem pressure_queries (P : Sheet G) (K : MapPrices) (i j : ℕ) :
    Teller.Grants (Testing.query P K i j) := grants _

/-- Use before evaluating possible questions. This grant part of the
price order works at every K proposed, not only after K, L suffice for
a Directed or similar. -/
theorem pressure_pricing (P : Sheet G) (K : MapPrices) :
    ∃ k : ℕ → ℕ, ∀ n : ℕ → ℕ, (∀ i, k i ≤ n i) → ∀ D : Rolls { P with floorL := n },
    ∀ m ≥ (0:ℝ), ∀ Θ : Protection D, ∀ V : Supply.Delays Θ, ∃ W : Supply.Delays Θ,
      W.shells=V.shells ∧ W.growth=V.growth ∧ W.scaleEntry=V.scaleEntry ∧ V.betaEntry ≤ W.betaEntry ∧
        ∃ F : ℕ → ℕ → ℝ, Testing.Ringing K F W ∧ ∀ i, ∀ j, F i j ≥ m :=
  Bid.pricing_order P K (pressure_queries P K)
end YM.Next.Fluctuations
