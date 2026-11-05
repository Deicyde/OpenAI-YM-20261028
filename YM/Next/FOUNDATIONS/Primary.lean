import YM.Integrated
import YM.LocalH.Haar
import YM.Source.ODE
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04


/-!
# RSetup and RAuthors: producers

Quantified over the **actual closed matrix group image** of the statement of
CLOSED (in particular, works for all G with G.Simple).

No Schedule, β,
History, future funding, or continuum data needed for the productions (as
opposed to consumers).

Keep the KernelChoices,
Haar chart, Hol, Frames and all sections here fixed in the application, not
period-, L-, or stage-dependent.

* The analytic exp chart ratio is for **G.probHaar**, map identity in LocalRatio
  on the real open ball.

The branching constants in KernelChoices are uniform
  for the actual shared-choice lattice branch.

This component refers to those
  analytic and finite-geometry foundations, not to the separate later
  stationary-phase/loop problem.

Frames
  uses the real, filtered polynomial basis of Labels.

Then realize T.Sound on
  these very choices by consumption of Integrated.source_sections.

`Credit` queries only valid
  BudgetPoints (in particular 6 ≤ k, 2 ≤ P, 0 < threshold ≤ 1,
  equality allowed in health tests); the table is defined also at small
  parameters, and estimates include the zeroth derivative, weight bound d=0 and
  any Side including one and placements with wrapping.

`Sound.projects`
  is on Cover; it does *not* assert an unambiguous periodic placement
  for arbitrary small sides.

Stencil room and enough calendar orders,
  powers and columns in an actual history will have to be provided;
  we give a sufficiency lemma for the Section aspect of that interface.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Foundations

open Lattice Wilson RG Precision Source
open scoped Topology Matrix.Norms.Frobenius BigOperators

section Branch

variable (G : Gauge)

/-- Fix these choices before L, at any requested penalty. -/
def kernel (κ : ℝ) (hκ : 0 < κ) : KernelChoices := (Axial.viable G κ hκ).choose



theorem branches (κ : ℝ) (hκ : 0 < κ) (P : Patch) : P.Branches (kernel G κ hκ) G :=
  (Axial.viable G κ hκ).choose_spec.2 P





/-- One chart used throughout (fixed absolute normalization). -/
def chart : ChartRatio G := (LocalH.actual G).choose

/-- Includes positivity of radius and scale, exp-map injectivity there,
`ContDiffAt ℝ ω` in ball, anchored positive density, and the change of
variables with density `x ↦ scale * J x` from Euclidean Color volume
to **probability** Haar restricted to exp of ball. -/
theorem chart_ok : LocalRatio (chart G) := (LocalH.actual G).choose_spec

end Branch

section Authors
variable (G : Gauge)

/-- Constructed using the actual all-time transport existence theorem. -/
def hol : Hol G := Classical.choice (Hol.exists_ode G)



/-- Use `Labels.frames G` (extend the basis recursively) unchanged. Here is
an actual realization of the previously conditional sections service. -/
theorem learns : Bid.Learns G (hol G) (Labels.frames G) :=
  Integrated.source_sections G (hol G) (Labels.frames G)

def localSection : ∀ d : ℕ, SectionData ((Labels.frames G).level d) := (learns G).builds.choose

theorem sound (d : ℕ) : (localSection G d).Sound (hol G) :=
  (learns G).builds.choose_spec.1 d

theorem valuation (d : ℕ) : Bid.pop (localSection G d) :=
  (learns G).builds.choose_spec.2.1 d

theorem credit_mono {d : ℕ} {F : Labels.Frame G d} (X : SectionData F) {k P : ℕ} {a b : ℝ}
    (h : Bid.Credit X k P a) (hab : a ≤ b) : Bid.Credit X k P b := by
  intro B hk hP n o i
  obtain ⟨hr, hp, hh⟩ := h B hk hP n o i
  have hw := mul_le_mul_of_nonneg_right hab (pow_nonneg B.threshold_pos.le (F.grades i).2)
  exact ⟨hr, hp.trans hw, fun U hU l hl he => (hh U hU l hl he).trans hw⟩

private def basePrice (q : ℕ × ℕ × ℕ) :=
  ((learns G).builds.choose_spec.2.2 q.1 q.2.1 q.2.2).choose

private def queries (D : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (D+1)).product ((Finset.range (D+1)).product (Finset.range (D+1)))

private theorem mem_queries (q : ℕ × ℕ × ℕ) (D : ℕ) :
    q ∈ queries D ↔ q.1 ≤ D ∧ q.2.1 ≤ D ∧ q.2.2 ≤ D := by simp [queries]

/-- An ex ante price (no claim of efficiency), for weights/order/power ≤ D. -/
def price (D : ℕ) : ℝ := 1 + ∑ q ∈ queries D, max 0 (basePrice G q)

theorem price_one_le (D : ℕ) : 1 ≤ price G D :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => le_max_left _ _)



theorem priced {d k P D : ℕ} (h : d ≤ D) (hk : k ≤ D) (hp : P ≤ D) :
    Bid.Credit (localSection G d) k P (price G D) := by
  have hC : Bid.Credit (localSection G d) k P (basePrice G (d,k,P)) :=
    ((learns G).builds.choose_spec.2.2 d k P).choose_spec
  have he : (d,k,P) ∈ queries D := (mem_queries ..).mpr ⟨h, hk, hp⟩
  unfold price
  apply credit_mono G _ hC
  exact le_trans (le_max_right 0 _) (le_trans
    (Finset.single_le_sum (f := fun i => max 0 (basePrice G i)) (fun i _ => le_max_left _ _) he)
    (le_add_of_nonneg_left zero_le_one))

/-- part of psect, no health test, independent even of budget.
Both on the infinite cover and, hence, placed (both versions are actual
point bounds, not essential-supremum bounds). -/
theorem full_value_bound (d : ℕ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ i : ((Labels.frames G).level d).Index,
      (∀ U : CoverConfig G, ‖(localSection G d).evaluate (Pi.single i 1) U‖ ≤ c) ∧
      (∀ n : Side, ∀ o : Site n, ∀ U : Config G n,
        ‖(localSection G d).places (Pi.single i 1) o U‖ ≤ c) := by
  have he (i : ((Labels.frames G).level d).Index) :
      ∃ c : ℝ, 0 ≤ c ∧ ∀ U : CoverConfig G,
        ‖(localSection G d).evaluate (Pi.single i 1) U‖ ≤ c := by
    obtain ⟨b,hb⟩ := (isCompact_range
      ((localSection G d).continuous_evaluate (Pi.single i 1)).norm).bddAbove
    exact ⟨max b 0, le_max_right _ _, fun U => (hb ⟨U,rfl⟩).trans (le_max_left _ _)⟩
  choose c hc hh using he
  refine ⟨1 + ∑ i, c i, le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hc i), fun i => ?_⟩
  have hv : c i ≤ 1 + ∑ i, c i := le_trans
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i))
    (le_add_of_nonneg_left zero_le_one)
  exact ⟨fun U => (hh _ U).trans hv, fun n o U => (hh _ (expandAt o U)).trans hv⟩

/-- Side length sufficient for placement at any anchor (same `20` buffer
as `Family.Makes`). -/
def minSide (d : ℕ) : ℕ := (localSection G d).stencil.sup fun x =>
  Finset.univ.sup fun i => 20*((x i).natAbs+1)

theorem stencil_price {d M : ℕ} (h : minSide G d ≤ M) (x : Cover)
    (hx : x ∈ (localSection G d).stencil) (i : Axis) : 20*((x i).natAbs+1) ≤ M := by
  refine le_trans ?_ h
  unfold minSide
  exact le_trans (Finset.le_sup (f:=fun j : Axis => 20*((x j).natAbs+1)) (Finset.mem_univ i))
    (Finset.le_sup (f:=fun v : Cover => Finset.univ.sup fun j : Axis => 20*((v j).natAbs+1)) hx)

/-- Conditional use in the existing history interfaces. The numerical
hypotheses to be funded by the later planner/history nodes are explicit.
All costs used here for X with a requested order and power can be priced
before L. Doesn't assert these schedule inequalities have been paid together
(or even that the order/power are sufficiently growing); no Paper.Clocks. -/
theorem refLi (H : RG.History G) (r : ℕ → ℕ)
    (orders : ∀ d, d+3 ≤ H.levels.clock.J (r d) ∧ ∀ i, r d ≤ i →
      d+1 ≤ (H.levels.params i).order ∧ d ≤ (H.levels.params i).power)
    (fit : ∀ d N p, r d ≤ N → minSide G d ≤ (H.S.side N p).val)
    (income : ∀ d N, r d ≤ N →
      price G (max (H.levels.params N).order (H.levels.params N).power) ≤
        (H.levels.params N).columns) :
    Bid.RefLi H (Labels.frames G) (localSection G) (hol G) r := by
  refine ⟨sound G, orders, (fun d N p h => stencil_price G (fit d N p h)), fun d N h => ?_⟩
  have hd := (orders d).2 N h
  exact credit_mono G _ (priced G (hd.2.trans (le_max_right _ _))
    (le_max_left _ _) (le_max_right _ _)) (income d N h)

end Authors
end YM.Next.Foundations
