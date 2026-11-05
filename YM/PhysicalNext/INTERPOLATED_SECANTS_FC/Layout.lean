import YM.AnalyticBridge.VERIFIED_RESET_STEP.Trays
import YM.Further.LOCAL_LOG_JETS.Price
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Grades


/-!
# One spelling sufficient for the secant estimates before projection

Interoperability via precisely the
VerifiedReset.Collection early representation ABI below.

Algebraic/log reconstruction
on this spelling, on the TRUE all-store integrals including common scalar and tag reads,
is a separate upstream task (not a theorem of this file).

Includes four low coupling powers
(relative to y=hatBetaFine), designated complete supports/anchor assignments BEFORE sending
coupons, masks and restoration of forced terms.

Expansion of exclusion replenishments
uses `exp(negative log occurrence) - 1`, i.e. at most one Mayer selection per tuple
address (the tuple itself has ordered positions and Ursell coefficient/symmetry factor,
not an unordered set of atoms).

Incidence to an excluded original forced support is
required even inside a larger attachment word.

Low alignment discrepancy exponents here are
field readings with the SAME real flags throughout and zero on entirely good supports.

Choosers and prices of the low approximants on the unary and binary log tuples (all terms
including exceptions, not just degree ≤2 free terms!) remain major open inputs; no claim that
taking an ordinary unprofiled moment on another geometry produces them on these footprints.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open RG Wilson Lattice Filter Function Push.AbsoluteSums Ursell Further.LogJets AnalyticBridge.VerifiedReset
open scoped Classical Matrix.Norms.Frobenius Topology BigOperators

/-- `atom` after first integration of unforced species (possibly anchored variants of them);
`seed` the forced species from that SAME expansion. `aligned` independent-basis outputs of
the pure low (incoming E=K=0) path & curvature-jet cancellations, `attachment` supports of
remaining clipping/movement discrepancies BEFORE final §freset itself. Never discard extra
flags when pricing. -/
structure Placement (G : Gauge) (n : Side) (ι κ : Type*) where
  atom : ι → RegularAddress n
  seed : κ → ForcedAddress G n
  aligned : ℕ → RegularAddress n
  attachment : ℕ → Support n
  visited i : (attachment i).Nonempty
  padding : ℕ → ForcedAddress G n

abbrev Bulk (ι : Type*) := Clusters ι ⊕ ℕ
abbrev Letter (ι κ : Type*) := κ ⊕ Bulk ι

variable {G : Gauge} {n : Side} {ι κ H : Type*}
namespace Placement
variable (A : Placement G n ι κ)

def site (i : ι) := (A.atom i).site
def reads (i : ι) := (A.atom i).support
def cluster (z : Clusters ι) : RegularAddress n :=
    ⟨A.site (z.2 none), foot A.reads z, covered A.reads z none ((A.atom _).anchor)⟩
def regular : Bulk ι → RegularAddress n := Sum.elim A.cluster A.aligned
def support : Letter ι κ → Support n := Sum.elim (fun i => (A.seed i).support) (Sum.elim (foot A.reads) A.attachment)
def region (s : Finset (Letter ι κ)) := s.biUnion A.support
def inventory (s : Finset (Letter ι κ)) := s.toLeft.biUnion (fun i => (A.seed i).inventory)

def assembled (s : Finset (Letter ι κ)) : Prop := Ac.Spark A.support s ∧ s.toLeft.Nonempty ∧
    (↑s.toLeft : Set κ).PairwiseDisjoint (fun i => (A.seed i).support) ∧ ∀ j∈s.toRight.toLeft,
      ∃ i∈s.toLeft, ¬ Disjoint (foot A.reads j) (A.seed i).support
abbrev Word := { s // A.assembled s }
lemma region_covers (s : A.Word) : (A.inventory s.val).Nonempty ∧ A.inventory s.val ⊆ A.region s.val := by
  obtain ⟨i,hi⟩ := s.property.2.1
  have he (i) (hi : i∈s.val.toLeft) := Finset.subset_biUnion_of_mem (fun i => (A.seed i).inventory) hi
  refine ⟨(A.seed i).inventory_ne.mono (he i hi),?_⟩
  intro x hx; obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨Sum.inl i,Finset.mem_toLeft.mp hi,(A.seed i).inventory_sup hx⟩

def combined (p : BudgetPoint) (w : A.Word) : ForcedAddress G n where
  support := A.region w.val
  inventory := A.inventory w.val
  inventory_ne := (A.region_covers w).1
  inventory_sup := (A.region_covers w).2
  extraTest U := ∀ i∈w.val.toLeft, (A.seed i).eligible p.threshold U
abbrev Hard := A.Word ⊕ ℕ
def forced (p : BudgetPoint) : A.Hard → ForcedAddress G n := Sum.elim (A.combined p) A.padding
instance [Countable ι] [Countable κ] : Countable A.Word := by unfold Word; infer_instance
end Placement

structure Shelf (G : Gauge) (n : Side) (ι κ : Type*) extends Placement G n ι κ where
  eOrder : ℕ ≃ Bulk ι
  kOrder : ℕ ≃ toPlacement.Hard
namespace Shelf
variable (S : Shelf G n ι κ)

def canonical (A : Placement G n ι κ) [Countable ι] [Countable κ] : Shelf G n ι κ :=
  ⟨A,Extra.Iteration.numbering _,Extra.Iteration.numbering _⟩
def listing (p : BudgetPoint) : Collection.Listing G n :=
    ⟨S.toPlacement.regular ∘ S.eOrder,S.toPlacement.forced p ∘ S.kOrder⟩
end Shelf

/-- Currency BEFORE projection/§freset. `approx` on original tuple supports, at z.1<2 only;
remaining exact unforced signed term at this tuple goes into logRead. `fresh` after aligning,
including the discrepancy to the clipped/output paths at the stipulated normalization.
Low indicator corrections `move` go into the new compulsory merger at actual flags. H
is the incoming payload type (not an output dial); `unforced` are pre-mask extensions. -/
structure Content (G : Gauge) (n : Side) (ι κ H : Type*) where
  unforced : ℝ → H → ι → Field G n
  forced : ℝ → H → κ → Field G n
  approx : Clusters ι → Powers G n
  fresh : ℕ → Powers G n
  move : ℕ → Powers G n
namespace Content
variable (f : Content G n ι κ H)

def peeled (y b : ℝ) (z : Clusters ι) := if z.1<2 then polynomial (f.approx z) (b/y) else 0
def processed (y b : ℝ) (j : ℕ) := polynomial (f.fresh j) (b/y)
variable (A : Placement G n ι κ)

def raw (b : ℝ) (h : H) (z : Clusters ι) := part A.reads (f.unforced b h) z
def tail (y b : ℝ) (h : H) (z : Clusters ι) := f.raw A b h z - f.peeled y b z
def logarithm (y b : ℝ) (h : H) : Bulk ι → Field G n := Sum.elim (f.tail A y b h) (f.processed y b)

def correction (p : BudgetPoint) (y b : ℝ) (j : ℕ) (U : Config G n) := if Healthy p.threshold (A.attachment j) U then
    0 else polynomial (f.move j) (b/y) U
/-- Compensating for omitted positive-log terms by inserting our MASKED negative-log
terms (only in words where their support in fact meets an original seed). -/
def discrepancy (p : BudgetPoint) (y b : ℝ) (h : H) (U : Config G n) : Bulk ι → ℝ := Sum.elim
    (fun z => masked p.threshold (foot A.reads z) (f.raw A b h z) U) (fun j => f.correction A p y b j U)
def priceField (p : BudgetPoint) (y b : ℝ) (h : H) (U : Config G n) : Letter ι κ → ℝ :=
    Sum.elim (fun j => f.forced b h j U) (fun z => Real.exp (f.discrepancy A p y b h U z)-1)
def gathered (p : BudgetPoint) (y b : ℝ) (h : H) (w : A.Word) (U : Config G n) :=
    if (A.combined p w).eligible p.threshold U then ∏ j∈w.val,f.priceField A p y b h U j else 0
def hard (p : BudgetPoint) (y b : ℝ) (h : H) : A.Hard → Field G n := Sum.elim (f.gathered A p y b h) (fun _ => 0)

def issue (S : Shelf G n ι κ) (p : BudgetPoint) (y b : ℝ) (h : H) : Collection.Source G n :=
    ⟨f.logarithm S.toPlacement y b h ∘ S.eOrder,f.hard S.toPlacement p y b h ∘ S.kOrder⟩

end Content
end YM.PhysicalNext.InterpolatedSecantsFc
