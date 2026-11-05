import YM.R2I.Campaign.Clock

/-! One post-length numerical request for a countable, already selected family.
At profile index j only the finite square n,i <= j is requested.  Every fixed
demand is eventually covered by the original deep profile map.  The request
changes only betaEntry and persists under every later DelayLe. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeDiagonalClockRequest
open Filter Lattice RG RG.Supply Push.PriceCompiler
open PhysicalNext.Repeat.Legato.R2I
open scoped BigOperators

def envelope (F : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (j + 1), ∑ i ∈ Finset.range (j + 1), |F n i|

private lemma envelope_one (F : ℕ → ℕ → ℝ) (j : ℕ) :
    1 ≤ envelope F j := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun n _ =>
    Finset.sum_nonneg fun i _ => abs_nonneg (F n i))

private lemma entry_le (F : ℕ → ℕ → ℝ) {n i j : ℕ}
    (hn : n ≤ j) (hi : i ≤ j) : |F n i| ≤ envelope F j := by
  have h1 : |F n i| ≤ ∑ k ∈ Finset.range (j + 1), |F n k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (F n k))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have h2 : (∑ k ∈ Finset.range (j + 1), |F n k|) ≤
      ∑ q ∈ Finset.range (j + 1), ∑ k ∈ Finset.range (j + 1), |F q k| :=
    Finset.single_le_sum
      (fun q _ => Finset.sum_nonneg fun k _ => abs_nonneg (F q k))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  exact h1.trans (h2.trans (le_add_of_nonneg_left zero_le_one))

private lemma double_log {E b : ℝ} (h : Real.exp (Real.exp E) ≤ b) :
    E ≤ Real.log (Real.log b) := by
  have h1 : Real.exp E ≤ Real.log b := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos (Real.exp E)) h
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos E) h1

variable {G : Gauge}

/-- The first index is chosen separately for each fixed demand, on the SAME
Levels.  No assertion is made about all demands at a fixed finite stage. -/
def PaidRequests (F : ℕ → ℕ → ℝ) (A : Levels G) : Prop :=
  (∀ m, 1 ≤ 1 + Real.log (Real.log (A.clock.hatBeta m))) ∧
  ∀ n, ∃ first : ℕ, ∀ m, first ≤ m → ∀ i, i ≤ A.clock.J (m + 1) →
    |F n i| ≤ 1 + Real.log (Real.log (A.clock.hatBeta m))

/-- A single admissible numerical delay buys every fixed member eventually,
including both original adjacent profile indices. -/
theorem eventuallyPaid (F : ℕ → ℕ → ℝ) :
    EventuallyPaid (PaidRequests (G := G) F) := by
  intro s P θ V
  let X : Delays θ :=
    { V with betaEntry := fun j => max (V.betaEntry j) (Real.exp (Real.exp (envelope F j))) }
  refine ⟨X, ⟨?_, le_rfl, le_rfl, le_rfl⟩, ?_⟩
  · intro j
    exact le_max_left _ _
  intro D hD B J A hA
  have he (m : ℕ) : envelope F (A.clock.J (m + 1)) ≤
      Real.log (Real.log (A.clock.hatBeta m)) := by
    apply double_log
    exact (le_max_right (V.betaEntry (A.clock.J (m + 1))) _).trans
      ((hD.beta (A.clock.J (m + 1))).trans (hA.pays m))
  refine ⟨?_, ?_⟩
  · intro m
    exact le_add_of_nonneg_right
      ((zero_le_one.trans (envelope_one F _)).trans (he m))
  intro n
  have hn : ∀ᶠ m : ℕ in atTop, n ≤ A.clock.J m :=
    A.fits.deep.eventually (eventually_ge_atTop n)
  obtain ⟨first, hfirst⟩ := eventually_atTop.1 hn
  refine ⟨first, ?_⟩
  intro m hm i hi
  have hnj : n ≤ A.clock.J (m + 1) :=
    (hfirst m hm).trans (A.fits.mono (Nat.le_succ m))
  exact (entry_le F hnj hi).trans
    ((he m).trans (le_add_of_nonneg_left zero_le_one))

end YM.Integration.NativeDiagonalClockRequest
end
