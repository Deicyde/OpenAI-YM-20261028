import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.MultiNext.VACUUM_STABILITY.Arrival.Projection
import YM.MultiNext.VACUUM_STABILITY.Chapters


set_option warningAsError false

/-!
# Complete support components in the first system

All inputs to the post-first reclosure of FirstGas. One usual raw alphabet (may have blank
labels and extra vertices to implement them). Genuine choices: overlapping queries at an
unmarked physical location cannot be split into two components by quoting independent integrals.
Assembly reverses on the ACTUAL address system when it has these supports and eligibility, a
requirement on the physical producer retained below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Component
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {V : Type} {n : Side} {I : Type}

abbrev Fruit := ℕ ⊕ ℕ

-- Convention in this layer: inl unforced, inr forced component outputs.

def ends (B : Brush V G n) : Fruit → Support n := Sum.elim (fun i => (B.u i).zone) (fun i => (B.pack i).zone)

def calls (B : Brush V G n) : Fruit → Grade V := Sum.elim (fun i => (B.u i).stamp.name) (fun i => (B.d i).name)

/-- Raw atoms include all variants, independent of z or derivative order used to estimate a
letter. Full vertices. A polydisc marker exponent expansion has already proliferated variants;
contributors keep one choice in actual packets. Spark implies no splitting of its addresses. -/
structure Pasture (I : Type) (B : Brush V G n) where
  sites : I → Support n
  origin i : (sites i).Nonempty
  hue : I → Grade V
  bud : Fruit → Finset I
  unique : Function.Injective bud
  connected i : Ac.Spark sites (bud i)
  lives i : ends B i = (bud i).biUnion sites
  full i : calls B i = ∑ j∈bud i,hue j

variable {B : Brush V G n}

namespace Pasture
variable (A : Pasture I B)

def valid (L : Support n) (s : Finset Fruit) :=
    (s : Set Fruit).PairwiseDisjoint (ends B) ∧ s.toRight.biUnion (fun i => (B.pack i).flagsAt) = L

def expand (s : Finset Fruit) := s.biUnion A.bud

def linked (s : Finset Fruit) := (s:Set Fruit).PairwiseDisjoint (ends B)

def recovers (s : Finset Fruit) (b : Finset I) := s.image A.bud=Ac.Parts A.sites b

lemma separates {s : Finset Fruit} (hs : linked (B:=B) s) : A.recovers s (A.expand s) := by
  have he : A.expand s=(s.image A.bud).biUnion id := by rw [Finset.image_biUnion]; rfl
  rw [he,recovers]; symm
  apply Ac.separates
  · intro b hb; obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hb; exact A.connected _
  intro i hi j hj hn; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hj
  exact (show Disjoint ((A.bud a).biUnion A.sites) ((A.bud b).biUnion A.sites) by
    rw [←A.lives,←A.lives]; exact hs ha hb (fun H => hn (H ▸ rfl)))

lemma retrieves {s : Finset Fruit} {b : Finset I} (he : A.recovers s b) : A.expand s=b := by
  rw [←Ac.reconstruct A.sites b,←he,Finset.image_biUnion]; rfl

lemma known {s u : Finset Fruit} {b : Finset I} (he : A.recovers s b) (hh : A.recovers u b) : s=u :=
  Finset.image_injective A.unique (he.trans hh.symm)

lemma apart (s : Finset Fruit) (hh : linked (B:=B) s) : (s : Set Fruit).PairwiseDisjoint A.bud := by
  intro i hi j hj hn; apply Finset.disjoint_left.mpr; intro x hx ht; obtain ⟨u,hu⟩:=A.origin x
  have hp : Disjoint (ends B i) (ends B j) := hh hi hj hn; rw [A.lives,A.lives] at hp
  exact Finset.disjoint_left.mp hp (mem_biUnion.mpr ⟨x,hx,hu⟩) (mem_biUnion.mpr ⟨x,ht,hu⟩)

variable [Fintype V]

def consumes (B : Brush V G n) (P : BudgetPoint) (U : Config G n) (z : V→ℂ) : Fruit → ℂ :=
    Sum.elim (fun i => (B.u i).echoes P z U) fun i => (B.d i).tell z U

def plant (B : Brush V G n) (P : BudgetPoint) (U : Config G n) (z : V → ℂ) (s : Finset Fruit) :=
    if valid (B:=B) (flags P.threshold U) s then ∏ i∈s,consumes B P U z i else 0

/-- b raw-atom selection. Code below computes its term, zero on incompatible, retaining
any internal eligibility through B's components and marks. Requirement on the REAL analytic
expansion giving the value below; cannot assert from geometry here. -/
def view (P : BudgetPoint) (U : Config G n) (z : V → ℂ) (b : Finset I) :=
    if h : ∃ s, A.recovers s b then plant B P U z h.choose else 0

lemma picture (b : Finset I) (s : Finset Fruit) (h : A.recovers s b) (P : BudgetPoint) (U : Config G n) (z : V→ℂ) :
    A.view P U z b = plant B P U z s := by
  unfold view; split; rename_i hp
  · rw [A.known hp.choose_spec h]
  rename_i he; exact False.elim (he ⟨_,h⟩)

lemma hues (b : Finset I) (P : BudgetPoint) (U : Config G n) (z : V→ℂ) :
    A.view P U z b = Stamp.beat (∑ i∈b,A.hue i) z * A.view P U 1 b := by
  unfold view; split; rename_i hp
  · let s := hp.choose; have hs : A.recovers s b := hp.choose_spec
    unfold plant; split; rename_i he
    · have h : linked (B:=B) s := he.1
      have ht (i) : consumes B P U z i = Stamp.beat (calls B i) z * consumes B P U 1 i := by
        obtain i|i := i
        · simp_rw [consumes,Sum.elim_inl,SmoothLetter.tint]; simp [calls,Stamp.beat]
        simp [consumes,calls,Stamp.tells,Stamp.beat]
      have hx := A.retrieves hs
      have hb : (∑ i∈b,A.hue i) = ∑ i∈s,calls B i := by
        rw [←hx,expand,Finset.sum_biUnion (A.apart s h)]; exact sum_congr rfl fun i _ => (A.full _).symm
      rw [hb,Stamp.beat_pile,← Finset.prod_mul_distrib]; exact prod_congr rfl fun i _ => ht i
    rw [mul_zero]
  rw [mul_zero]



-- support equivalence reindexing, also when pricing by norm
lemma carries {X : Type} [AddCommMonoid X] [TopologicalSpace X] (x : X) (P : BudgetPoint) (U : Config G n) (z : V→ℂ)
    (f : ℂ→X) (he : f 0=0) : HasSum (fun i => f (plant B P U z i)) x ↔ HasSum (fun i => f (A.view P U z i)) x := by
  let g := fun i => f (plant B P U z i)
  let t := fun i => f (A.view P U z i)
  have h {i j} (he : A.recovers i j) : g i=t j := by dsimp only [g,t]; rw [A.picture _ _ he]
  have hf i (hi : i∈support g) : valid (B:=B) (flags P.threshold U) i := by by_contra hz; exact hi (by simp [g,plant,hz,he])
  let L (i : support g) := A.expand i.val
  have hz i : A.recovers i.val (L i) := A.separates (hf i.val i.property).1
  let r (i : support g) : support t := ⟨L i, fun ht => i.property ((h (hz i)).trans ht)⟩
  have hr : Injective r := by intro a b h; have hu : L a=L b:=congrArg Subtype.val h; exact Subtype.ext (A.known (hu ▸ hz a) (hz b))
  have hp : Surjective r := by
    intro j; have ht : ∃ i,A.recovers i j.val := by by_contra hz; exact j.property (by simp [t,view,hz,he])
    obtain ⟨i,hi⟩:=ht; have he' : i∈support g := fun H => j.property ((h hi).symm.trans H)
    exact ⟨⟨i,he'⟩,Subtype.ext (A.retrieves hi)⟩
  exact (Equiv.ofBijective r ⟨hr,hp⟩).hasSum_iff_of_support (fun i => (h (hz i)).symm) -- orientation
end Pasture
end YM.Multi.Vacuum.Component
