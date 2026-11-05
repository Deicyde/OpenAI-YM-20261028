import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Emitter
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.MaskMotion
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Walls
import YM.Push.SECTOR_MEASURE.Payment
import YM.SectorNext.RECONNECTED_LOCALITY.Leads
import YM.Work.B18

/-!
# An option for reconciling the placements of different V functions

This is an occurrence representation. Batches can contain several occurrences on the
same footprint. Simple case: just pass each incoming log-address to its own output label
with no movement. Substantive issue: for cancellation between old unforced and committed
path terms may want to put them on DIFFERENT (larger) indicators and split into several
different batches e.g. around their low jets . Implement any **fixed finite**
program of this type with finite fibres. Require actual charge tests everywhere along
the route, but determine the output terms, signs and supports *by the program*. There is
NO requirement to supply a representation or an equality-merger input. This won't prove
that the hard-field or low-curvature estimates really pay enough for any such program.
Does not depend on being able to furnish good normalized bounds (e.g. a small H) on its
output. See also `Tape.works` for separate convergence currency.

* Shield to a larger support, with correction.
* Optionally split the unmasked function into subterms after shielding, using the stored
  ordered test rays of each actual term, projecting onto local reference stencils. The
  **entire** remainder is computed and always sent. Even directions of order zero (maybe
  for a constant) use the actual function; there is no requirement that it equal any
  Taylor polynomial or that an estimate applies to a dropped suffix. `length` checked
  for the PREMASK germs; use only with `sound` receipts for their true extensions. No
  direction comparison prices for free. Could also permit other preprogrammed local
  projection procedures in future versions. The program with no such projections already
  suffices for the *equality* part.
* Send all pieces along their common field evaluations to finite-fibre batches according
  to a prechosen layout. Enroll/enlarge whole supports when reanchoring (no moving physical
  payload by a translation independently). Each output mask change in this procedure must ALSO be accounted
  on the failed-indicator ledger.

Keep the whole tape as the historical dictionary if the support history is queried,
including if projection data happens to be zero or classifies several equal numerical
values. The positivity/continuity/size of the overall theory isn't an input here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas
open RG Lattice Wilson Function Filter Finset
open Push.LogIdentity SectorNext.Reconnect
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {p : BudgetPoint}

/-- Possible local charges for grouping. Work in the TRUE germs (length test BEFORE
projection), with the exact chosen local template: any path basis used here has to
include its complete supports. Arguments and templates fixed through every parameter
pass. `shield` below includes this `S`. -/
structure Ray (G : Gauge) (n : Side) (p : BudgetPoint) (S : Support n) where
  test : List (Directions G n)
  length : test.length ≤ p.order
  lamp : SheetFunction G n
  costSite : p.Regular S lamp

/-- One stage: a support map for each leg AND a recovery address for each indicator
comparison. The marker-free tests for this implementation already require the listed
shield. Keep them even for attempts on flags. -/
structure Roller (G : Gauge) (p : BudgetPoint) (X Y : Plate n) where
  shield : X.letter → Support n
  protects i : X.range i ⊆ shield i
  arity : X.letter → ℕ
  ray i : Fin (arity i) → Ray G n p (shield i)
  send : (Σ i : X.letter, Option (Fin (arity i))) → Y.letter
  receive : Y.letter → Finset (Σ i : X.letter, Option (Fin (arity i)))
  exact i j : i ∈ receive j ↔ send i = j
  passes i : shield i.fst ⊆ Y.range (send i)

namespace Plate
variable (P : Plate n)
def sound (E : P.Ink G) (p : BudgetPoint) := ∀ i,p.Regular (P.range i) (E i)

/-- For the topology and stagewise price proofs. -/
def ward (E : P.Ink G) (p : BudgetPoint) (b : P.letter → ℝ) :=
  ∀ i V, Healthy p.threshold (P.range i) V → ‖E i V‖ ≤ b i

def Pattern (E : P.Ink G) (p : BudgetPoint) :=
    ∃ b, P.ward E p b ∧ Summable b

variable {P} {b : P.letter → ℝ} {E : P.Ink G}





lemma ward_combine {X : Plate n} {F : X.Ink G} {a : X.letter → ℝ} (h : P.ward E p b) (h' : X.ward F p a) :
    (P.combine X).ward (Sum.elim E F) p (Sum.elim b a) :=
  fun i => Sum.recOn i h h'
end Plate

namespace Roller

variable {X Y : Plate n} (T : Roller G p X Y)

abbrev Bit := Σ i : X.letter, Fin (T.arity i)
abbrev Case := Σ i : X.letter, Option (Fin (T.arity i))

/-- Elevated plate for the old function during projection tests. Keep its anchor. -/
def held : Plate n := ⟨X.letter,fun i => ⟨(X.label i).site,T.shield i,T.protects i (X.label i).anchor⟩⟩



/-- Cut terms not freely postulated. Generate from THIS local function (e.g. in a
low-order lens). `extra` marks one proposed stencil projection. -/
def extra (E : X.Ink G) (i : T.Bit) : SheetFunction G n :=
  let R := T.ray i.fst i.snd
  fun V => leftDerivs (E i.fst) R.test 1 * R.lamp V

def portion (E : X.Ink G) (i : T.Case) : SheetFunction G n :=
    match i.snd with
    | some j => T.extra E ⟨i.fst,j⟩
    | none => fun V => E i.fst V - ∑ j,T.extra E ⟨i.fst,j⟩ V



lemma stenciled (i) {E : X.Ink G} (h : X.sound E p) : p.Regular (T.shield i.fst) (T.portion E i) := by
  have he (i) : p.Regular (T.shield i.fst) (T.extra E i) := Snip.scaled _ (T.ray _ _).costSite
  rcases i with ⟨i,_|j⟩; swap; exact he ⟨i,j⟩
  have hh (s : Finset (Fin (T.arity i))) : p.Regular (T.shield i) (fun U => ∑ j∈s,T.extra E ⟨i,j⟩ U) := by
    induction s using Finset.induction_on with
    | empty => simp only [sum_empty]; exact Snip.still _
    | insert j s h ih => simp_rw [sum_insert h]; exact Snip.adjoin (he ⟨i,j⟩) ih
  exact Snip.subtract (Snip.swell (h i) (T.protects i)) (hh _)

def batch (E : X.Ink G) : Y.Ink G := fun j V => ∑ i∈T.receive j,T.portion E i V
lemma sound_batch {E : X.Ink G} (h : X.sound E p) : Y.sound (T.batch E) p := by
  intro j
  suffices ∀ s ⊆ T.receive j, p.Regular (Y.range j) (fun V => ∑ i∈s,T.portion E i V) from this _ (Finset.Subset.refl _)
  intro s hs
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact Snip.still _
  | insert i s hi ih =>
    have he : T.send i=j := (T.exact ..).1 (hs (mem_insert_self ..))
    simp_rw [sum_insert hi]
    exact Snip.adjoin (Snip.swell (T.stenciled i h) (he ▸ T.passes i)) (ih fun _ hv => hs (mem_insert_of_mem hv))

/-- Need a correction at BOTH of these address moves. -/
def blush : Slip n := {
    letter := X.letter ⊕ T.Case
    reach := Sum.elim T.shield (fun i => Y.range (T.send i))
    full i := Sum.recOn i (fun j=>⟨_,(T.held.label j).anchor⟩) fun j => ⟨_,(Y.label (T.send j)).anchor⟩ }

def smear (E : X.Ink G) : T.blush.Ink G := Sum.elim
    (MaskMotion.diff X.range T.shield p E)
    (MaskMotion.diff (fun i : T.Case => T.shield i.fst) (fun i => Y.range (T.send i)) p (T.portion E))

lemma stamped {E : X.Ink G} (h : X.sound E p) : T.blush.Vouched p (T.smear E) := by
  have he := fun i => MaskMotion.diff_used X.range T.shield p E i (T.protects i) (h i)
  have ht := fun i => MaskMotion.diff_used (fun i : T.Case => T.shield i.fst) (fun i => Y.range (T.send i)) p
    (T.portion E) i (T.passes i) (T.stenciled i h)
  constructor
  · rintro (i|i); exact (he i).2.1; exact (ht i).2.1
  · rintro (i|i); exact (he i).2.2; exact (ht i).2.2
  rintro (i|i); exact (he i).1; exact (ht i).1

lemma hits (E : X.Ink G) : T.blush.Lands p (T.smear E) := by
  have h {X Y : Support n} (h : X ⊆ Y) (f : SheetFunction G n) (U : Config G n) (he : Healthy p.threshold Y U) :
      masked p.threshold X f U = masked p.threshold Y f U := by
    rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (Finset.disjoint_of_subset_left h he)]
  rintro (i|i) V he hv
  · apply he
    change masked _ (T.shield i) _ _ - masked _ (X.range i) _ _ = 0
    exact sub_eq_zero.mpr (h (T.protects i) (E i) V hv).symm
  apply he
  change masked _ (Y.range (T.send i)) _ _ - masked _ (T.shield i.fst) _ _ = 0
  exact sub_eq_zero.mpr (h (T.passes i) (T.portion E i) V hv).symm

end Roller

/-- finite but any finite number of passes/still mask indices, G fixed. -/
inductive Tape (G : Gauge) (p : BudgetPoint) : Plate n → Plate n → Type 1 where
  | clear {X} : Tape G p X X
  | step {X Y Z : Plate n} (T : Roller G p X Y) (rest : Tape G p Y Z) : Tape G p X Z

namespace Tape
variable {X Y : Plate n}

def finalPlate {X Y : Plate n} : Tape G p X Y → X.Ink G → Y.Ink G
  | .clear, E => E
  | .step T g, E => g.finalPlate (T.batch E)

def signed {X Y : Plate n} : Tape G p X Y → Slip n
  | .clear => ⟨Empty,Empty.elim,fun i => Empty.elim i⟩
  | .step T g => T.blush.combine g.signed

def bill {X Y : Plate n} : (f : Tape G p X Y) → X.Ink G → f.signed.Ink G
  | .clear,_,i => Empty.elim (show Empty from i)
  | .step T g,E,i => Sum.elim (T.smear E) (g.bill (T.batch E)) i

end Tape
end YM.PhysicalNext.PreAtlas
