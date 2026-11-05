import YM.Extra.MULTISOURCE_TRAJECTORIES.Localization
import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
/-!
# Fixed-torus capacities of the exact histories

Works even with exact positional coincidences (separate markers). Shrinking
radii here in general depend on everything incl N, current level, period and
the number of markers. Definitely not a proof of affordably large radii for
RMixed. No compatibility of these costs across levels or extractions assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Wilson RG Lattice Overlay Marker Mix Function Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {V : Type} [DecidableEq V] {R : Census V}

lemma budget_smaller {ι : Type*} {f g : ι → ℝ} {u v : ℝ} (h : SumBudget g u) (hf : ∀ i,0 ≤ f i)
    (hh : ∀ i,f i ≤ g i) (he : u≤v) : SumBudget f v := by
  have hs := h.2.1.of_nonneg_of_le hf hh
  exact ⟨hf,hs,(hs.tsum_le_tsum hh h.2.1).trans (h.2.2.trans he)⟩








variable {G : Gauge} {n : Side} {P : Rep G n}





namespace Layers.Prices
variable {α : Type*} [Fintype α] [Nonempty V] {X : Layers P R α} (Q : X.Prices)




end Layers.Prices

namespace Probes
variable {N p j : ℕ} {C : Family G} (Q : Probes C V N p) [Fintype V] (R : Census V) (B : Windows (C.side j p))


end Probes
end YM.Extra.Trajectories
