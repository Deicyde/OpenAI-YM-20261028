import YM.Planned.ATOM_FORCED_ESTIMATE.Bulk
import YM.Planned.ATOM_FORCED_ESTIMATE.Letters
import YM.Planned.ATOM_FORCED_ESTIMATE.Outside
import YM.Push.LOCAL_SPLITTING.Padding


/-!
# Unmarked local prerequisites at the output

Book = data of E fstgas and of the unmarked indicator moves (normalization, potential
moves, etc.). Vocabulary for vacuum reclosure, including a *cavity identity* below.
That extra compatibility with the chosen output `Rep` is required of the vacuum
producer on this approach, not a consequence of `History.Selected`. Read it as equality
with the old merger *outside any one avoided region*, not as permission to run a
different vacuum construction or to omit all forced factors. Often available by just
keeping the overlap components with original supports and book histories. Artificial
later enlargements/re-preparations could require proving a different adapter instead.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.Forced
open Function Filter Lattice Wilson RG Source MeasureTheory Push.Local Push.AbsoluteSums
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n : Side}

structure Stop (n : Side) where
  support : Support n
  inventory : Support n
  live : inventory.Nonempty
  sub : inventory ⊆ support

/-- `weight` = initial forced d, `extra` = obligatory test footprints of unmarked
post-log *attachment* corrections (not the negative missing addresses themselves).
They may have additional tests inside their values. Read directly on one output field.
`base` is the common scalar times the first-system unmarked exponential piece. -/
structure Book (G : Gauge) (n : Side) where
  base : Config G n → ℝ
  bulk : Bulk G n
  stop : ℕ → Stop n
  weight : ℕ → Config G n → ℝ
  spot : ℕ → Support n
  spot_ne i : (spot i).Nonempty
  extra : ℕ → Config G n → ℝ

namespace Book
variable (K : Book G n) (B : BudgetPoint)
abbrev site (i : ℕ) := (K.stop i).support
abbrev inventory (i : ℕ) := (K.stop i).inventory
abbrev Atoms := ℕ ⊕ (ℕ ⊕ Bulk.Node)

def skin : Atoms → Support n := Sum.elim K.site (Sum.elim K.spot K.bulk.region)

def source (V : Config G n) : Atoms → ℝ := Sum.elim (fun j => K.weight j V) (Sum.elim (fun j => K.extra j V) (K.bulk.withdraw B V))



structure Uses : Prop where
  cylinder (i) : UsesFinal B.threshold (K.site i) (K.weight i)
  symmetry (i) : GaugeInvariant (K.weight i)
  meas (i) : Measurable (K.weight i)
  relies (i) : UsesFinal B.threshold (K.spot i) (K.extra i)
  gauge (i) : GaugeInvariant (K.extra i)
  borel (i) : Measurable (K.extra i)
  vanishes (i) (V) : Healthy B.threshold (K.spot i) V → K.extra i V = 0

/-- Accounts BEFORE either merger (and the projected cost of omission
factors, paid from unmarked prices at appropriate exponents in `accounts`). -/
structure Accounts (f : Atoms → ℝ) (γ δ q : ℝ) : Prop where
  uses : K.Uses B
  forced (i V) : ‖K.weight i V‖ ≤ f (.inl i)
  attachments (i V) : ‖K.extra i V‖ ≤ f (.inr (.inl i))
  negative (i) : B.Regular (K.bulk.region i) (K.bulk.expTerm i) ∧
    B.supBounds (K.bulk.center i) (K.bulk.region i) (K.bulk.expTerm i) (f (.inr (.inr i)))
  ready : Trees.Ready K.skin B.B f ((B.supportExponent+2)+1) γ δ q
  unrestricted (V : Config G n) : ∃ t u r : ℝ,
    Trees.Ready K.bulk.support B.B (fun i => ‖K.bulk.read B V i‖) 0 t u r

variable {K B}



variable (K)

/-- First-gas selection of unmarked FORCED components outside `Y`. -/
def Dock (Y D : Support n) (s : Finset ℕ) := (s : Set ℕ).PairwiseDisjoint K.site ∧
    (∀ i∈s, Disjoint Y (K.site i)) ∧ s.biUnion K.inventory = D \ Y

def Needs (Z : Support n) (s : Finset ℕ) (i : Bulk.Node) := ¬ Disjoint (Z ∪ s.biUnion K.site) (K.bulk.region i)

def Picks (Z : Support n) (s : Finset Atoms) := ∀ i ∈ s.toRight.toRight, K.Needs Z s.toLeft i

variable (B)



def External (Y : Support n) (V : Config G n) (s : Finset Atoms) :=
    K.Dock Y (flags B.threshold V) s.toLeft ∧ K.Picks ∅ s ∧ Disjoint Y (s.biUnion K.skin)

def old (Y : Support n) (V : Config G n) (s : Finset Atoms) : ℝ := if K.External B Y V s then ∏ i∈s,K.source B V i else 0







/-- Real, unmarked prerequisites on the VERY Rep intended for the source. -/
structure Cavity (R : Rep G n) : Prop where
  bulk V : K.base V * Gas.total K.bulk.graph (K.bulk.read R.p V) = Real.exp (R.exponent V) * ∑' t : Finset ℕ, ∏ i∈t,K.extra i V
  gas (Y : Support n) V : outsideGas R.activities R.p Y V = ∑' s, K.old R.p Y V s

namespace Accounts
variable {K B} {f : Atoms → ℝ} {γ δ q : ℝ} (h : K.Accounts B f γ δ q)
include h

















lemma reads (i : Atoms) : UsesFinal B.threshold (K.skin i) (fun V => K.source B V i) := by
  rcases i with i|(i|i)
  · exact h.uses.cylinder _
  · exact h.uses.relies _
  intro V W huv ht; change K.bulk.withdraw .. = K.bulk.withdraw ..; rw [← Complex.ofReal_inj,K.bulk.expTerm_mask, K.bulk.expTerm_mask]
  exact uses_mask _ (h.negative i).1.sites V W huv ht
end Accounts
end Book
end YM.Planned.Forced
