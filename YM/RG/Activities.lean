import YM.RG.Masks
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Regular and forced density activity format

Denotational representation . Not a quotient by `eval`. Countably
many addresses indexed by Nat with zero padding; all indexed data fixed in the
history. `supp` is the actual support used for compatibility. Final flag reads
can test all flags in `supp`; they force the enlarged `inspected` support for
payload dependence. `inventory` and `eligible` stay fixed for *both* vacuum and
source coefficients when that address is used; include any extra tests in `eligible`
or use separate labels with zero vacuum coefficient. (In constructions with more
internal data or workspace queries ensure that these footprints include them;
this API doesn't constrain how one cooks up admissible addresses or how much to
pad outside their footprint.)
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG

open Lattice Wilson MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {n : Side} {G : Gauge}

/-- Affine directions set in canonical lift. Curl tests only imposed with
nonwrapping supports. -/
def IsAffineDirection (o : Site n) (u : Directions G n) : Prop :=
    ∃ (a : Axis → G.Color) (d : Axis → Axis → G.Color),
      ∀ e : Edge (Site n), u e = a e.2 + ∑ i : Axis, lift (e.1 - o) i • d e.2 i

def logHessian (F : Config G n → ℝ) (x y : Directions G n) : ℝ :=
  iteratedFDeriv ℝ 2 (fun A : Directions G n => F (increment 1 A)) 0 ![x,y]

structure RegularAddress (n : Side) where
  site : Site n
  support : Support n
  anchor : site ∈ support

structure ForcedAddress (G : Gauge) (n : Side) where
  support : Support n
  inventory : Support n
  inventory_ne : inventory.Nonempty
  inventory_sup : inventory ⊆ support
  extraTest : Config G n → Prop

namespace ForcedAddress

variable (a : ForcedAddress G n)

/-- Internal eligibility. Vacuum terms outside this predicate are zero. -/
def eligible (t : ℝ) (U : Config G n) :=
  a.support ∩ flags t U = a.inventory ∧ a.extraTest U
end ForcedAddress

/-- Absolute mass certificate; not a comparison of a bare `tsum`. -/
def SumBudget {ι : Type*} (f : ι → ℝ) (c : ℝ) : Prop :=
  (∀ i, 0 ≤ f i) ∧ Summable f ∧ ∑' i, f i ≤ c

structure Activities (G : Gauge) (n : Side) where
  reg : ℕ → RegularAddress n
  forced : ℕ → ForcedAddress G n
  E : ℕ → Config G n → ℝ
  K : ℕ → Config G n → ℝ
namespace Activities
variable (A : Activities G n) (p : BudgetPoint)

structure RegularFamily : Prop where
  smooth : ∀ i, p.Regular (A.reg i).support (A.E i)
  at_flat : ∀ i, A.E i 1 = 0
  vanish : ∀ i, Nonwrapping (A.reg i).support (A.reg i).site →
    ∀ x y, IsAffineDirection (A.reg i).site x → IsAffineDirection (A.reg i).site y →
      logHessian (A.E i) x y = 0

structure ForcedFamily : Prop where
  sym : ∀ i, GaugeInvariant (A.K i)
  symtest : ∀ i k U, (A.forced i).extraTest (gauge k U) ↔ (A.forced i).extraTest U
  meas : ∀ i, Measurable (A.K i)
  meas_test : ∀ i, MeasurableSet {U | (A.forced i).extraTest U}
  reads : ∀ i, UsesFinal p.threshold (A.forced i).support (A.K i)
  reads_test : ∀ i, UsesFinal p.threshold (A.forced i).support (A.forced i).extraTest
  permit : ∀ i U, A.K i U ≠ 0 → (A.forced i).eligible p.threshold U

/-- Transports of **whole** labels (point here is in the translated signed convention). -/
structure Moves (s : Signed) (b : Site n) where
  ep : Equiv.Perm ℕ
  kp : Equiv.Perm ℕ
  reg_site (i : ℕ) : (A.reg (ep i)).site = affine s b (A.reg i).site
  reg_support (i : ℕ) : (A.reg (ep i)).support = (A.reg i).support.image (affine s b)
  forced_support (i : ℕ) : (A.forced (kp i)).support = (A.forced i).support.image (affine s b)
  forced_inventory (i : ℕ) : (A.forced (kp i)).inventory = (A.forced i).inventory.image (affine s b)
  forced_tests (i : ℕ) (U : Config G n) : (A.forced (kp i)).extraTest U ↔ (A.forced i).extraTest (pull s b U)
  valuesE (i : ℕ) (U : Config G n) : A.E (ep i) U = A.E i (pull s b U)
  valuesK (i : ℕ) (U : Config G n) : A.K (kp i) U = A.K i (pull s b U)

def EBound (budget : ℝ) := ∃ b : ℕ → ℝ,
  (∀ i, p.supBounds (A.reg i).site (A.reg i).support (A.E i) (b i)) ∧
  ∀ x : Site n, SumBudget (fun i => if (A.reg i).site = x then p.mass (A.reg i).support (b i) else 0) budget

def KBound (budget : ℝ) := ∃ b : ℕ → ℝ,
  (∀ i, (0 ≤ b i) ∧ ∀ U, ‖A.K i U‖ ≤ b i) ∧
  ∀ x : Site n, SumBudget (fun i => if x ∈ (A.forced i).support then p.mass (A.forced i).support (b i) else 0) budget

structure Valid (δ w : ℝ) : Prop where
  regular : A.RegularFamily p
  forced : A.ForcedFamily p
  moves : ∀ s b, Nonempty (A.Moves s b)
  boundE : A.EBound p δ
  boundK : A.KBound p w

/-- Disjoint, exact coverage. Further predicates are internal, multiply by zero. -/
def admissible (U : Config G n) (b : Finset ℕ) :=
  (b : Set ℕ).Pairwise (fun i j => Disjoint (A.forced i).support (A.forced j).support) ∧
  b.biUnion (fun i => (A.forced i).inventory) = flags p.threshold U

theorem admissible_borel (b : Finset ℕ) : MeasurableSet {U | A.admissible p U b} := by
  unfold admissible
  by_cases hb : (b : Set ℕ).Pairwise (fun i j => Disjoint (A.forced i).support (A.forced j).support)
  · simp only [hb, true_and, eq_comm]
    exact flags_measurable_eq ..
  simp [hb]

def gasOccurrence (b : Finset ℕ) (U : Config G n) : ℝ := by
  classical
  exact if A.admissible p U b then ∏ i ∈ b, A.K i U else 0

def gas (U : Config G n) := ∑' b : Finset ℕ, A.gasOccurrence p b U

def regularOccurrence (i : ℕ) : Config G n → ℝ := masked p.threshold (A.reg i).support (A.E i)
def additive (U : Config G n) := ∑' i : ℕ, A.regularOccurrence p i U

/-- Local sanity check: in all-good no fake payloads. -/
theorem gas_one {U : Config G n} (he : flags p.threshold U = ∅) : A.gas p U = 1 := by
  unfold gas
  rw [tsum_eq_single ∅]
  · have h : A.admissible p U ∅ := by simp [admissible,he]
    simp [gasOccurrence,h]
  intro b hb
  have h : ¬ A.admissible p U b := by
    intro had
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hb
    obtain ⟨x, hx⟩ := (A.forced i).inventory_ne
    have hv : x ∈ flags p.threshold U := by rw [← had.2]; exact Finset.mem_biUnion.mpr ⟨i,hi,hx⟩
    simp [he] at hv
  simp [gasOccurrence,h]
end Activities
end YM.RG
