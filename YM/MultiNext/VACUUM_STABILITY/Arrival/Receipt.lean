import YM.MultiNext.VACUUM_STABILITY.Deploy

set_option warningAsError false

/-!
# Actual scalar arrivals at a committed step

Anchor budgets at exact `BudgetPoint`. No assumption on holomorphically changing the scalar v,
or geometry/branches/clips. Convert ANY list of permitted strokes to a single history/list of
ordinary polynomial letters, independent of z. Keep X genealogy for projected support test at
`Curves.Stability`. K variations on permitted packs; zero entries not a charge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Arrival
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock Source
open Jets Hits
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {V : Type} {n : Side}

structure Rates1 (n : Side) where
  constant : ℝ
  major : ℕ → ℝ
  minor : Pack n → ℝ

/-- A single incoming stroke, already priced. -/
structure Stroke (G : Gauge) (n : Side) where
  letter : ℕ → Support n
  reg : ℕ → Config G n → ℂ
  d : Pack n → Config G n → ℂ
  fiat : ℂ
  rate : Rates1 n

namespace Stroke
variable (s : Stroke G n)

def pulse (P : BudgetPoint) : Pulse G n := (fun U => s.fiat+∑' i,masked P.threshold (s.letter i) (s.reg i) U,s.d)

/-- For follower charges use Programs issuing the norm at regular readout BEFORE all
U-mask multiplications. For hard charges retain all inventory, separate final flag halo. -/
structure Authorized (P : BudgetPoint) (x : Site n) (κ k : ℝ) : Prop where
  ok : 0 ≤ k
  base : ‖s.fiat‖ ≤ s.rate.constant ∧ s.rate.constant ≤ k
  wears i : x∈s.letter i ∧ P.Regular (s.letter i) (s.reg i) ∧ P.supBounds x (s.letter i) (s.reg i) (s.rate.major i)
  paint : SumBudget (fun i => P.mass (s.letter i) (s.rate.major i)) k
  bears i : Legible P i (s.d i) ∧ (s.d i≠0 → x∈i.zone) ∧ 0 ≤ s.rate.minor i ∧ ∀ U, ‖s.d i U‖ ≤ s.rate.minor i
  hard : ∑ i : Pack n,P.mass i.zone (s.rate.minor i) ≤ κ*k




end Stroke

abbrev Flock (V : Type) (G : Gauge) (n : Side) := V → Stroke G n

namespace Flock
variable (F : Flock V G n)

section
variable [Fintype V]


end

structure Attended (P : BudgetPoint) (D : V → Pulse G n) (o : V → Site n) (k : V→ℝ) (κ : ℝ) : Prop where
  authorizations i : (F i).Authorized P (o i) κ (k i)
  fact i : (F i).pulse P=D i

section
variable {A : Type*} (ref : V→Option A) (S : V → ℕ → Support n)

def Silent := ∀ i,ref i=none → (F i).fiat=0 ∧ (F i).letter=S i


end
end Flock
end YM.Multi.Vacuum.Arrival
