import YM.Next.FLUCTUATIONS.Grants
import YM.Next.FLUCTUATIONS.Sector
import YM.Push.ABSOLUTE_SUMS.Delay
import YM.Work.A15


/-!
# Grant → absolute seed-packet sum, on one oriented step

Works wherever the Teller hypotheses have been paid.

We do NOT assert
a new sectorization or the per-packet estimate for all OTHER factors
in such a sectorization.

We also
give a price for sums of `Sector` integrals, explicitly relative to
the common volume prefactor (kept OUTSIDE the budget), and explicitly
conditional on the outgoing multiplier expense.

Without a local
factor construction/estimates, the latter is not expected to be small
for arbitrary global multipliers, and isn't a claimed bound on the
actual pushforward density.

All costs post-L unless stated otherwise. `β` is a real actual band
parameter; `x` and tests use the coarse **hat** parameter as in
`Teller.Grants`. `V` arbitrary. All estimates for tree-slice integrals
use their actual orientations and likelihoods. No one claims summing
unnormalized copies over choices of TREE slices; a tree gauge is
chosen (or separate probability averages would be needed and must
keep the same shared data). The combinatorial forests are different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Grant
open Lattice Wilson RG Pressure Pressure.Stores Pressure.Teller Tree
  MeasureTheory Next.Fluctuations Packets Delay Filter
open scoped BigOperators Topology ENNReal Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Orientation and per-seed actual gain condition. No combinatorial or
integral conclusion hidden here. -/
def Earned (T : Tube G S) (μ x W : ℝ) := ∀ (F : Forest S.ratio) (A : Stores S)
    (U : Config G f) (k : S.Choices) (V : Config G c), SliceSet S F U → Plot A U k V x W →
    μ*(fiery G x S.patch.L)^2*A.shares ≤ A.assessed T x U (S.prediction U k) V

def credit (β μ x : ℝ) (G : Gauge) (L : Side) : ℝ := β*(μ*fiery G x L^2)

/-- Same grant BEFORE seeing any cost growth/cap comparison after L.
One can then pay these numerical gates by delay. No RLevel construction. -/
theorem order (P : Teller G) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ᶠ W : ℝ in atTop, 0 < W ∧
    ∃ μ : ℝ, 0 < μ ∧ ∀ l d : ℕ, ∀ u a D z : ℝ, 0 < u → 0 ≤ a → 0 ≤ D → z < 2 →
    ∀ᶠ x : ℝ in atTop, 0 < betaF G x L ∧
      (∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L →
        100*(1+radiusB x) ≤ c.val → P.Funds S T → Earned T μ x W) ∧
      ∀ β spend C : ℝ, u*betaF G x L ≤ β →
        let B := radiusB x; let M := hatWin G L μ u x; let q := retained G L μ u x
        let cost := D*Delay.bill G L x^d*fineMonitor G L x^z
        spend ≤ cost → 0 ≤ C → C ≤ Real.exp cost →
        fit L l B a spend (credit β μ x G L) q ∧
          ∀ m : ℕ, totalCharge L C l B q m ≤ Real.exp (-M/4*(max 1 m:ℕ)) := by
  obtain ⟨n,h⟩ := (grants P).precedes
  refine ⟨n,fun L hL => (eventually_gt_atTop (0:ℝ)).and ((h L hL).mono ?_)⟩
  intro W hw; obtain ⟨μ,hμ,he⟩ := hw
  refine ⟨μ,hμ,fun l d u a D z hu ha hD hz => ?_⟩
  filter_upwards [he.late,shift_pos G L,fits G L l hμ hu ha hD d hz] with x hx hc hh
  refine ⟨hc,fun c f S T hS hm hT F A U k V hy hk => ?_,fun β s C hβ he hf hb => ?_⟩
  · rw [hS]; exact hx _ _ S hS hm T hT F A U k V hy hk
  exact hh s (credit β μ x G L) C he (Delay.comparison G L hc hμ β hβ) hf hb

section Pointwise
variable {P : Teller G} {T : Tube G S} {μ x W β : ℝ}

/-- Multiplier still on the ACTUAL sector/test at U. -/
def paid (T : Tube G S) (x W β : ℝ) (U : Config G f) (V : Config G c)
    (g : Stores S → S.Choices → ℝ) (A : Stores S) (k : S.Choices) :=
  if Plot A U k V x W then |g A k| * Real.exp (-β*A.assessed T x U (S.prediction U k) V) else 0








end Pointwise

section Peel
open Next.Fluctuations.Sector
variable {P : Teller G} {T : Tube G S} {μ x W β : ℝ}



def expense (T : Tube G S) (x W β : ℝ) (F : Forest S.ratio) (V : Config G c)
    (g : Stores S → S.Choices → F.Slice G → ℝ) (A : Stores S) :=
  ∑ k, ∫ b in onSector A F x W k V,
    g A k b * outgoing A T β x k V (F.drape b) ∂F.order G


end Peel
end YM.Push.AbsoluteSums.Grant
