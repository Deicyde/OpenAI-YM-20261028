import YM.Next.EXTRACTION.Mixture
import YM.Ovens.Coffee
import YM.Push.CORRECTED_COLUMNS.Pieces
import YM.Work.C06
import YM.Work.F02.Path
/-!
# Attach permitted omissions

Unscaled steps have many (not necessarily disjoint, and possibly infinitely
many) smaller corrections. Select each marked omission syllable or
failed-mask letter at most once. Keep the banned-by relation to the
*actual* hard records; not every overlap has to have caused an omission.
This allows tracking omitted log components e.g. by the core of a record,
without treating its reclosed scalar halo as the core. Physical applicability
requires that producer identity, not assumed from mere geometry!

Generalization of `YM.Push.CORRECTED_COLUMNS.Pieces`, `.Invited` and
`.Rendezvous`, proof adapted from there. It is the inclusion of an old K and
the retention of original support disjointness/coverage inside the joined
description that will let us keep its gain. No division by a K. Enlarging the
vacuum dictionary only at comparison; still booking by the full union.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Set Function MeasureTheory Lattice Wilson RG Marker
open Push.Corrected
open Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V α : Type*} [DecidableEq V] {R : Census V}
variable {P : Rep G n} {o : V → Site n}

/-- Letter `i` permitted with the chosen K configuration iff it has some
`contact` with a member. Letters don't need to be disjoint from each
other. In this module contacts fixed by addresses; keep enough labels
before assembly. -/
structure Dock (P : Rep G n) (o : V → Site n) (R : Census V) (α : Type*) where
  patch : α → Support n
  warm i : (patch i).Nonempty
  contact : α → ℕ → Prop
  meets i j : contact i j → ∃ x ∈ patch i, x ∈ oldSites P j
  letter : α → Config G n → Poly R
  hot i U : (letter i U).part R.quiet=0
  reads i : Width.LocalCharge P.p o (patch i) (letter i)

namespace Dock
variable (d : Dock P o R α) (F : Original P o R)

def permit (s : Finset ℕ) (i : α) := ∃ j ∈ s,d.contact i j
def location : ℕ ⊕ α → Support n := Sum.elim (oldSites P) d.patch
def skin (p : Finset (ℕ ⊕ α)) := p.biUnion d.location
abbrev cargo (P : Rep G n) (p : Finset (ℕ ⊕ α)) := UnionK.inventory P p

def Glued (p : Finset (ℕ ⊕ α)) := Ac.Spark d.location p ∧
    (p.toLeft : Set ℕ).PairwiseDisjoint (oldSites P) ∧ ∀ i ∈ p.toRight, d.permit p.toLeft i
abbrev Item := {s // d.Glued s}










def amount (i : ℕ ⊕ α) := Sum.elim F.value d.letter i



def exactAt (p : d.Item) (U : Config G n) := d.skin p.val∩flags P.p.threshold U=cargo P p.val
open scoped Classical in
def filled (p : d.Item) (U : Config G n) := if d.exactAt p U then ∏ i∈p.val,d.amount F i U else 0






end Dock
end YM.Further.ThresholdSourceRestart
