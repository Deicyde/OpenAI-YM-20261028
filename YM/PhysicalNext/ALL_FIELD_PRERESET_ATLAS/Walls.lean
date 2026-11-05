import YM.Bid.Loan
import YM.Ovens.Coffee
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Entry
import YM.SectorNext.RECONNECTED_LOCALITY.Lines


/-!
# Pre-reset addresses and terms before final `ℕ` numbering

For reusing the pricing/spelling interfaces. In the production below keep the layouts
with all ancestor addresses interpreted by the occurrence compiler (no existential
enumeration from the countability of evaluated values); interfaces taking a palette
must use that layout. `Plate` for unforced, `Depot` for forced and `Slip` for attaching corrections
(their exponentiated factorial convention will distinguish even repeated occurrences on
one address).
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas
open RG Lattice Wilson SectorNext.Reconnect Push.LogIdentity
open scoped Matrix.Norms.Frobenius ContDiff Classical BigOperators Topology

variable {G : Gauge} {n : Side}

structure Plate (n : Side) where
  letter : Type
  [enumerated : Countable letter]
  label : letter → RegularAddress n

structure Depot (G : Gauge) (n : Side) where
  letter : Type
  [enumerated : Countable letter]
  label : letter → ForcedAddress G n

structure Slip (n : Side) where
  letter : Type
  [enumerated : Countable letter]
  reach : letter → Support n
  full (i : letter) : (reach i).Nonempty

attribute [instance] Plate.enumerated Depot.enumerated Slip.enumerated

namespace Plate
variable (M : Plate n)
abbrev Ink (G : Gauge) := M.letter → SheetFunction G n
abbrev range i := (M.label i).support
def maskedLog (p : BudgetPoint) (E : M.Ink G) (V : Config G n) (i : M.letter) :=
    masked p.threshold (M.range i) (E i) V

def binder (E : M.Ink G) : Room G n M.letter := ⟨M.label,E⟩

def combine (X : Plate n) : Plate n := {
    letter := M.letter ⊕ X.letter
    label := Sum.elim M.label X.label }
end Plate

namespace Depot
variable (M : Depot G n)
abbrev Ink := M.letter → SheetFunction G n
abbrev range i := (M.label i).support
abbrev need i := (M.label i).inventory

/-- Set/forced gas. -/
def sell (p : BudgetPoint) (K : M.Ink) (V : Config G n) :=
    gasTerm M.range M.need (flags p.threshold V) fun i => K i V

/-- Separate the forced topology/cylinder predicates from all turn- and price-requests.
Each earlier compatibility needs to be in the given K term for sales to be valid. -/
structure Tenants (p : BudgetPoint) (K : M.Ink) : Prop where
  gauge i : GaugeInvariant (K i)
  testGauge i (k : Site n → G.El) (V : Config G n) :
    (M.label i).extraTest (Lattice.gauge k V) ↔ (M.label i).extraTest V
  usesInk i : UsesFinal p.threshold (M.range i) (K i)
  usesProbe i : UsesFinal p.threshold (M.range i) (M.label i).extraTest
  expenses i : Measurable (K i)
  probes i : MeasurableSet {V | (M.label i).extraTest V}
  permits i V : K i V ≠ 0 → (M.label i).eligible p.threshold V

def binder (K : M.Ink) : Brand G n M.letter := ⟨M.label,K⟩

lemma binder_sees (p : BudgetPoint) (K : M.Ink) (V : Config G n) :
    (M.binder K).record p V = M.sell p K V := by
  ext i
  unfold Brand.record sell gasTerm
  congr 1 -- classical `if`
end Depot

namespace Slip
variable (M : Slip n)
abbrev Ink (G : Gauge) := M.letter → SheetFunction G n

structure Vouched (p : BudgetPoint) (F : M.Ink G) : Prop where
  localizes i : UsesFinal p.threshold (M.reach i) (F i)
  gauge i : GaugeInvariant (F i)
  expenses i : Measurable (F i)

/-- Crucial when using in exponent equality between atlas views. At a fixed V.
This is *not* required of a generic restoration for a missing cluster. -/
def Lands (p : BudgetPoint) (F : M.Ink G) := ∀ i V,
    F i V ≠ 0 → ¬Healthy p.threshold (M.reach i) V

def combine (X : Slip n) : Slip n := {
    letter := M.letter ⊕ X.letter
    reach := Sum.elim M.reach X.reach
    full i := Sum.recOn i M.full X.full }

lemma Vouched.append {M X : Slip n} {p : BudgetPoint} {f : M.Ink G} {g : X.Ink G}
    (h : M.Vouched p f) (h' : X.Vouched p g) : (M.combine X).Vouched p (Sum.elim f g) :=
  ⟨fun i => Sum.recOn i h.localizes h'.localizes,fun i => Sum.recOn i h.gauge h'.gauge,
    fun i => Sum.recOn i h.expenses h'.expenses⟩
lemma Lands.append {M X : Slip n} {p : BudgetPoint} {f : M.Ink G} {g : X.Ink G}
    (h : M.Lands p f) (h' : X.Lands p g) : (M.combine X).Lands p (Sum.elim f g) :=
    fun i => Sum.recOn i h h'
end Slip
end YM.PhysicalNext.PreAtlas
