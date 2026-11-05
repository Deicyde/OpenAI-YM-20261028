import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.RingTheory.Nilpotent.Exp
import YM.Ac.Table
import YM.Analysis.Polydisc
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Org.Theatre
import YM.Pressure.Seeds
import YM.Work.A05.Read

/-!
# At station k: joint attachment to a `Bands`

Addresses for actual orbit/frame of all copies, exact energies on old
representation without altering its K or swapping history.

Use hypothesis of
spare forced catalog in that vacuum.

Letter counts distinct.

Merged forms grouped by mode for
each *old-address/new-marker connected configuration*; doesn't produce,
e.g., a solution of stronger genealogy requirements unspecified here.

Same
threshold, marker and root orientation preferences as read in `Bands`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Push.GridApprox.Attach
open RG Lattice Wilson Cells MeasureTheory Function Filter Finset Ac Marker Overlay
open scoped Topology BigOperators

variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}

/-- Coarse cylinders already scaled for physical source insertion. One per
site marker, allow an independent global c too. Y includes whole support and
origin. -/
structure Plan {P : Rep G n} (a : Bands R P) where
  Y : V → Support n
  c : V → ℂ
  F : V → Config G n → ℂ
  good i : P.p.Regular (Y i) (F i)
  origin i : a.origins i∈ Y i

variable {P : Rep G n} {a : Bands R P} (I : Plan a)

abbrev Alphabet (V : Type*) := ℕ ⊕ V

def patch : Alphabet V → Support n := Sum.elim (fun i => (P.activities.forced i).support) I.Y

def peel (j : V) (U : Config G n) : ℂ := I.F j U - masked P.p.threshold (I.Y j) (I.F j) U

def leaf (l : Alphabet V) (U : Config G n) : Poly R := l.elim (fun i => a.each i U)
    (fun j => Poly.send (R.fire j) (peel I j U))

def sheet (s : Finset (Alphabet V)) := s.biUnion (patch I)

def flagsFor (P : Rep G n) (s : Finset (Alphabet V)) := s.toLeft.biUnion (fun i => (P.activities.forced i).inventory)

/-- Include even components with zero potential value. Never make two K
carriers within an admitted selection overlap. -/
def Kept (s : Finset (Alphabet V)) : Prop := s.toLeft.Nonempty ∧ Spark (patch I) s ∧
    ((s.toLeft : Set ℕ).PairwiseDisjoint (fun i => (P.activities.forced i).support))

def Fresh (s : Finset (Alphabet V)) : Prop := Kept I s ∧ s.toRight.Nonempty

abbrev Block := {s // Fresh I s}









/-- Need actual dormant names with these capabilities in P. Not a license
to create them in somebody else's path. `extraTest` still used for the OLD
carriers; for the new names assume unconditionally available. Order along P
unchanged. -/
structure Spares where
  tag : Block I → ℕ
  injective : Injective tag
  full j : (P.activities.forced (tag j)).support = sheet I j.val
  flags j : (P.activities.forced (tag j)).inventory = flagsFor P j.val
  plain j U : (P.activities.forced (tag j)).extraTest U
  idle j : P.activities.K (tag j)=0
  marks j i : a.entries (tag j) i = 0

variable {I} (T : Spares I)

open scoped Classical in
private def from? (q : ℕ) := if h : ∃ j, T.tag j=q then some h.choose else none

open scoped Classical in
private lemma from_inside (j : Block I) : from? T (T.tag j)=some j := by
  unfold from?; split_ifs with hx
  · rw [T.injective hx.choose_spec]
  exact False.elim (hx ⟨j,rfl⟩)

open scoped Classical in
private lemma from_outside (q : ℕ) (h : ∀ j, T.tag j ≠ q) : from? T q = none := by
  unfold from?
  split
  next he => obtain ⟨j,hj⟩ := he; exact False.elim (h j hj)
  rfl

def group (q : ℕ) : Finset (Alphabet V) := match from? T q with
    | some j => j.val
    | none => {Sum.inl q}

lemma group_inside (j : Block I) : group T (T.tag j) = j.val := by unfold group; rw [from_inside]
lemma group_outside (q : ℕ) (h : ∀ j, T.tag j≠q) : group T q={Sum.inl q} := by unfold group; rw [from_outside T q h]

lemma group_injective : Injective (group T) := by
  classical
  have hm (q : ℕ) (p : Block I) (e : group T q=p.val) : q=T.tag p := by
    by_cases h : ∃ j, T.tag j=q
    · obtain ⟨j,rfl⟩ := h; rw [group_inside] at e; exact congr_arg T.tag (Subtype.ext e)
    rw [group_outside T q (by tauto)] at e
    have ht := p.property.2
    rw [← e] at ht
    obtain ⟨j,hj⟩ := ht; simp at hj
  intro i j he; by_cases h : ∃ k, T.tag k=i
  · obtain ⟨k,rfl⟩ := h; rw [group_inside] at he; exact (hm j k he.symm).symm
  by_cases hh : ∃ k,T.tag k=j
  · obtain ⟨k,rfl⟩ := hh; rw [group_inside] at he; exact hm i k he
  rw [group_outside T _ (by tauto),group_outside T _ (by tauto)] at he; simpa using he



section output
variable [Nonempty V]

open scoped Classical in
/-- Addressed product is actually admitted. Components otherwise zero.
Other `extraTest`s remain via the old `a.each`. -/
def connection (j : Block I) (U : Config G n) : Poly R :=
    if (P.activities.forced (T.tag j)).eligible P.p.threshold U then ∏ l∈j.val, leaf I l U else 0

/-- Mark access names inside a new combined address. -/
def code (s : R.Mode) := (Fintype.equivFin R.Mode s).val

lemma code_inj : Injective (code (R:=R)) := fun _ _ h => (Fintype.equivFin _).injective (Fin.ext h)

open scoped Classical in
private def choice (R : Census V) (i : ℕ) := if h : ∃ s : R.Mode, s.val.Nonempty ∧ code s=i then some h.choose else none
lemma choice_in (s : R.Mode) (h : s.val.Nonempty) : choice R (code s)=some s := by
  classical
  unfold choice
  split_ifs with hx; exacts [congr_arg _ (code_inj hx.choose_spec.2),False.elim (hx ⟨s,h,rfl⟩)]
lemma choice_out (R : Census V) (i) (h : ∀ s : R.Mode, s.val.Nonempty → code s≠i) : choice R i=none := by
  classical
  unfold choice
  split
  next h' => obtain ⟨j,hj,he⟩ := h'; exact False.elim (h _ hj he)
  rfl

def shapes (V : Type*) [Fintype V] : ℕ ≃ Alphabet V :=
    letI := Classical.choice (nonempty_denumerable (Alphabet V))
    (Denumerable.eqv _).symm

def attached : Bands R P where
  origins := a.origins
  units := fun j => a.units j + I.c j
  support q := (shapes V q).elim a.support I.Y
  rays q := (shapes V q).elim a.rays R.fire
  H q := (shapes V q).elim a.H I.F
  marks q i := match from? T q with
      | none => a.marks q i
      | some _ => (choice R i).getD (R.fire (Classical.arbitrary V))
  entries q i := match from? T q with
      | none => a.entries q i
      | some j => match choice R i with
          | none => 0
          | some s => fun U => (connection T j U).part s

lemma mark_in (j : Block I) (s : R.Mode) (h : s.val.Nonempty) : (attached T).marks (T.tag j) (code s) = s := by
  dsimp only [attached]; rw [from_inside]; simp [choice_in s h]
lemma entry_in (j : Block I) (s : R.Mode) (h : s.val.Nonempty) : (attached T).entries (T.tag j) (code s) =
    fun U => (connection T j U).part s := by dsimp only [attached]; rw [from_inside]; simp [choice_in s h]
lemma mark_out (q : ℕ) (h : ∀ j, T.tag j≠q) (i) : (attached T).marks q i = a.marks q i := by dsimp only [attached]; rw [from_outside T q h]
lemma entry_out (q : ℕ) (h : ∀ j, T.tag j≠q) (i) : (attached T).entries q i = a.entries q i := by dsimp only [attached]; rw [from_outside T q h]
lemma entry_extra (j : Block I) (i) (h : ∀ s : R.Mode, s.val.Nonempty → code s ≠ i) :
    (attached T).entries (T.tag j) i=0 ∧ (attached T).marks (T.tag j) i = R.fire (Classical.arbitrary V) := by
  dsimp only [attached]; rw [from_inside]; simp [choice_out R i h]
end output
end YM.Push.GridApprox.Attach
