import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Body
import YM.Push.BETA_TRANSPORT.Score
import YM.Push.RELAY_DIFFERENCE.Lanes

set_option warningAsError false

/-!
# Taking the least absolute budget for fixed ink

Apparent issue with `Mute`: e.g., will it be enough to prove output estimates
parametrically for inputs of budget 1? (How about when the data we actually
used in constructing the comparison were paid on a different, MUCH larger
bill than later used to prove direction on the matched source?) Yes within
the same step, with the same reference data and the same step's transferred
derivative & weight norms. Can choose at least input budget. Include the real
zero case. No assertion that a zero-cost regular function must vanish off its
healthy domain.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource
open Function Filter MeasureTheory RG Wilson Lattice Labels Source
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open Body Push.RelayDifference
variable {G : Gauge} {n : Side} {e : ℕ} {F : Frame G e} {R : Rep G n} {o : Site n}
variable {U : GridU n} {D : Body F n} {κ r : ℝ}

structure Tally (o : Site n) (R : Rep G n) (U : GridU n) (D : Body F n) (κ r : ℝ) where
  energy : ℝ
  breath : ℝ
  seed : ℕ → ℝ
  stamp : ℕ → ℝ
  e_nn : 0 ≤ energy
  b_nn : 0 ≤ breath
  pay : energy+breath ≤ r
  k_pos : 0 < κ
  energyPay : SumBudget (fun i => R.p.mass (U i) (seed i)) energy
  breathPay : SumBudget (fun i => R.p.mass (R.activities.forced i).support (stamp i)) (κ*breath)
  sexp i : R.p.supBounds o (U i) (payload D i) (seed i)
  tag i : 0 ≤ stamp i ∧ ∀ x, ‖flag D i x‖ ≤ stamp i
lemma Tally.billed (T : Tally o R U D κ r) : cap o R U D κ r :=
  ⟨T.energy,T.breath,T.e_nn,T.b_nn,T.pay,T.k_pos,⟨T.seed,T.energyPay,T.sexp⟩,T.stamp,T.breathPay,T.tag⟩


section
variable (R o U) (f : ℕ → Config G n → ℂ)




end



lemma Tally.bare_cost (T : Tally o R U D κ r) : SumBudget T.seed T.energy ∧ SumBudget T.stamp (κ*T.breath) :=
  ⟨lower_budget T.energyPay le_rfl (fun i => (T.sexp i).1) (fun i => R.p.loMass _ _ (T.sexp i).1),
    lower_budget T.breathPay le_rfl (fun i => (T.tag i).1) (fun i => R.p.loMass _ _ (T.tag i).1)⟩





end YM.MultiNext.SignedSource
