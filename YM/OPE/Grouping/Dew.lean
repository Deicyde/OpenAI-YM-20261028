import YM.MergeProof.North.Dew
import YM.OPE.Grouping.Fibers

/-!
# Simultaneous collapses at a mesh scale

This accounting generalizes the proof for pairs in YM/MergeProof/North/Dew.lean
to a projection along fibers. The Deck prices a nonempty finite number of children
(not necessarily common across grouping regions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V] [Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable {S₀ : Type*} [Fintype S₀][DecidableEq S₀] {Δ : Fibers S₀ V}
structure Deck (V S₀ : Type*) [DecidableEq V][Fintype V] [DecidableEq S₀][Fintype S₀] (Δ : Fibers S₀ V) (I J : Type*) (G:Gauge)(n:Side) where
   mode_ : I⊕J→ (Bud S₀).Mode
   wick : I→ Support n
   spill : J→ Box n
   cover : I⊕J→ Support n
   toll : I⊕J→ Config G n→ℂ
   ash : I→Prop
   seat : V→Site n

namespace Deck
variable (D:Deck V S₀ Δ I J G n)
def wall := Sum.elim D.wick (fun i=>(D.spill i).1)
def roster (i):=(Δ.span (D.mode_ i)).val
def kiln : Kiln (I⊕J) V (Site n):=⟨D.roster,D.cover,Sum.elim D.ash fun _=>True⟩
structure Wet (t:ℝ):Prop where
   old i:D.wall i⊆ D.cover i
   buys i v:v∈D.roster i→D.seat v∈D.cover i
   clean i:(D.mode_ (.inl i)).val.Nonempty
   sure i: Sure (D.spill i)
   resid i U:D.ash i → D.toll (.inl i) U≠0 → ¬ Disjoint (D.cover (.inl i)) (flags t U)
   allows i U:D.toll (.inr i) U≠0 → (D.spill i).1 ∩ flags t U=(D.spill i).2
   plain i:D.roster (.inr i)=∅ → D.cover (.inr i)=(D.spill i).1
lemma spark (s:Finset (I⊕J)) (h:D.kiln.Mole s)(t:ℝ)(ht:D.Wet t): Ac.Spark D.cover s:=D.kiln.attends _ h (fun i _ j _ ⟨v,h1,h2⟩=> ⟨D.seat v,ht.buys _ _ h1,ht.buys _ _ h2⟩)

variable [DecidableEq I][DecidableEq J]
structure Ride (s:Finset (I⊕J)) :Prop where
   old : (s.toRight : Set J).PairwiseDisjoint (fun i=>(D.spill i).1)
   buys : Fits D.mode_ s
   ready : Δ.Pays (unionTag _ _ buys)
structure Cove (s:Finset (I⊕J)) :Prop extends D.Ride s where
   fire : D.kiln.Mole s
structure Comb (s:Finset (I⊕J)) :Prop extends D.Cove s where
   dry : ¬ D.kiln.Takes s
structure Tank (s:Finset (I⊕J)) :Prop extends D.Cove s where
   wet : s.toRight.Nonempty
abbrev Paper := {s:Finset (I⊕J)// D.Comb s}
abbrev Ink := {s:Finset (I⊕J)// D.Tank s}
abbrev Quills:= D.Paper ⊕ D.Ink
def glyph : D.Quills→Finset (I⊕J):= Sum.elim Subtype.val Subtype.val
def reach (s:Finset (I⊕J)) := s.biUnion D.cover
def stain (s:Finset (I⊕J)):= s.toRight.biUnion (fun i=>(D.spill i).2)
def fuse (s:Finset (I⊕J)) :Box n:= (D.reach s,D.stain s)
lemma run (i:D.Quills): D.Cove (D.glyph i):=by
   cases i
   next i=> exact i.property.toCove
   next i=> exact i.property.toCove
def plank (i:D.Quills):= unionTag _ _ (D.run i).buys
def quip (i:D.Quills) := Δ.span (D.plank i)
lemma paint (i:D.Quills): (D.quip i).val=(D.glyph i).biUnion D.kiln.mention:=Fibers.combines Δ _
omit [DecidableEq I] in
lemma blot (s: Finset (I⊕J)) (h:s.toRight.Nonempty):D.kiln.Takes s:=by obtain ⟨i,h⟩:=h; exact ⟨_,mem_toRight.mp h,trivial⟩
lemma tale : Injective D.glyph:=by
   have hh (i:D.Paper)(j:D.Ink):i.val≠j.val:=fun h=> i.property.dry (D.blot _ (h ▸ j.property.wet))
   rintro (i|j) (b|c) h
   · exact congr_arg _ (Subtype.ext h)
   · exact (hh i c h).elim
   · exact (hh b j h.symm).elim
   exact congr_arg _ (Subtype.ext h)
end Deck
end YM.MergeProof.Ribbons.Fibers
