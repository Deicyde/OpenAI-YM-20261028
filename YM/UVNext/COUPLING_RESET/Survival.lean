import YM.UVNext.COUPLING_RESET.Stability


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Simultaneous path tracking on surviving closed intervals

Enhance `Shoot.Reach` for this producer cut. Starting from any guaranteed
earnings uniformly throughout the requested bands, obtain one interval of
top Wilson parameters and one *whole* labelled unmarked path per parameter
through any requested depth, with exact unmarked Moves, no loss of accuracy,
and simultaneous norm/parameter continuity at all surviving indices on that
interval. Both endpoints at last level; interval may collapse where applicable
(e.g., coarsest request a singleton). Nothing asserts that these are the only
successful trajectories or that there's a continuously invertible relation
between initial and final beta: the inverse control of Response concerns a
different variable, the local correction dial. No ODE blowup assumption or
reapplication at illegal couplings. Need the full `Supplier`, not inferred
unconditionally.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.BetaTransport Lattice Wilson RG RG.Shoot RG.Supply Input Precision Filter Function Set
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {B : Directed G I Z K P} {η : ℕ → ℝ} {q : ResetPrices}
    {N m p : ℕ}

structure FamilyBand (B : Directed G I Z K P) (q : ResetPrices) (p N m : ℕ) (F : ℝ → Trail B.a p) (s : Set ℝ) : Prop where
  starts : ∀ x∈s, B.bake.Starter N p (F x N) ∧ (F x N).beta = x
  tracks j : m ≤ j → j ≤ N → Curve (B.a.budget j) (fun x => F x j) s
  prices : ∀ j, m ≤ j → j ≤ N → ∀ x ∈ s, Lives B.bake N j p (F x j) ∧ (F x j).beta ∈ band B.a j
  steps : ∀ j, m ≤ j → j < N → ∀ x ∈ s, B.Move N j p (F x j) (F x (j+1)) ∧ Accurate B q N j p (F x j) (F x (j+1))

variable {u s : Set ℝ} {F : ℝ → Trail B.a p}










end YM.UVNext.CouplingReset
