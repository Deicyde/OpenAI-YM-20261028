import YM.MultiNext.VACUUM_STABILITY.Log
import YM.MultiNext.VACUUM_STABILITY.MergeBound
import YM.MultiNext.VACUUM_STABILITY.Stamps

set_option warningAsError false

/-!
# Inputs at the post-integration, pre-log/reclosure stage

For the actual perturbed scalar density at one step (see connection in entry point).
NOT assumed from existing vacuum results. To produce with first-system integration (E eq:fstgas,
Fhitint, JMara-type estimates extended to ordinary amplitude monomials, repetitions included).
Explicit width and per-hit norms. Test convention exactly the represented vacuum.

The **Choice** of history in `RPaper` etc matters. Require compatible pointwise scalar
normalization, unmarked output inventory, and first derivative choices only, with same support
and partner conventions. Encode all the terms of the subsequent regular-identity moves from
vacuum reset and singleton readout (and therefore their FLAG-HITTING attachments) explicitly;
need estimates on those too. (How to produce them from more local recipes is another problem.)
Not a claim about arbitrary quote/paper paths.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Corona Alternatives Desk Rejoin
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V : Type} {n : Side} {G : Gauge}

structure SmoothLetter (V : Type) (G : Gauge) (n : Side) where
  zone : Support n
  stamp : Stamp V (Config G n)
  anchor : Site n
  origin : anchor ∈ zone

structure HardLetter (V : Type) (G : Gauge) (n : Side) where
  zone : Support n
  stamp : Stamp V (Config G n)
  kept : zone.Nonempty

/-- First-system unnormalized output before unrestricted log. -/
structure Brush (V : Type) (G : Gauge) (n : Side) where
  base : Config G n → ℂ
  pay : V → ℂ
  u : ℕ → SmoothLetter V G n
  pack : ℕ → Pack n
  d : ℕ → Stamp V (Config G n)

namespace Brush
variable (B : Brush V G n)

-- designated tape (can share in unmarked and first-source constructions)
def station : Chorus ℕ n := logTape (fun i => (B.u i).zone) (fun i => ⟨_,(B.u i).origin⟩)
lemma stat : Peeling (fun i => (B.u i).zone) univ ∅ B.station := tape_peeling ..

abbrev Line (B : Brush V G n) : Type := B.station.Root

def chapter (i : B.Line) : SmoothLetter V G n :=
    let w := B.station.tune.line i
    { zone := w.ground (fun i => (B.u i).zone), anchor := B.station.pole i
      origin := (B.station.poles _ 0 (B.stat.roots 0) i).1
      stamp := ⟨ (w.letters.map (fun i => (B.u i).stamp.name)).sum,
        Jets.stanza (fun i => (B.u i).stamp.ink) w⟩ }

variable [Fintype V]

-- occupied d supports, bulk u run outside

def ban (s : Finset ℕ) := s.biUnion (fun i => (B.pack i).zone)

def compulsory (L : Support n) (s : Finset ℕ) := (s:Set ℕ).PairwiseDisjoint (fun i => (B.pack i).zone) ∧
    s.biUnion (fun i => (B.pack i).flagsAt) = L

def entry (P : BudgetPoint) (z : V → ℂ) (U : Config G n) (s : Finset ℕ) :=
    if B.compulsory (flags P.threshold U) s then
      (∏ i∈s,(B.d i).tell z U) * BulkGas.Z (fun i => (B.u i).zone) (Finset.univ \ B.ban s)
          (fun i => masked P.threshold (B.u i).zone ((B.u i).stamp.tell z) U) else 0

def launch (q z : V → ℂ) := ∑ i, z i*q i

def flush (P : BudgetPoint) (z : V → ℂ) (U : Config G n) := B.base U *
    Complex.exp (launch B.pay z) * ∑' i,B.entry P z U i
end Brush

/-- Information about the chosen unmarked reset and chosen linear replacement/readout
terms on `active` singleton axes. Hard-letter sums are additional terms in the **positive**
forced exponent (not its negative), requiring a flag in the support. -/
structure Restock (V : Type) (G : Gauge) (n : Side) where
  outgoing : V → ℂ
  wrap : ℕ → SmoothLetter V G n
  sticker : ℕ → HardLetter V G n

namespace Restock
variable (B : Brush V G n) (C : Restock V G n)

-- omit and then attach negative clusters

def sealLog (P : BudgetPoint) : B.Line → HardLetter V G n := fun i =>
    let F := B.chapter i; { zone := F.zone, kept := ⟨_,F.origin⟩, stamp := ⟨F.stamp.name,
      -masked P.threshold F.zone F.stamp.ink⟩ }

abbrev Tail (B : Brush V G n) := B.Line ⊕ ℕ

def screws (P : BudgetPoint) : Tail B → HardLetter V G n := Sum.elim (sealLog B P) C.sticker

def mill (P : BudgetPoint) : Hearth n ℕ (Tail B) := ⟨B.pack,fun i => (screws B C P i).zone,
    fun i => (screws B C P i).kept⟩

def strand (P : BudgetPoint) : Hearth.Color ℕ (Tail B) → Grade V :=
    Sum.elim (fun i => (B.d i).name) fun j => (j.2+1) • (screws B C P j.1).stamp.name

/-- Generated on the actual cluster tape with the same d, seal, agenda and predicates; keep
partner addresses inside the construction. These are *merged* choices. -/

def glaze (P : BudgetPoint) (p : (mill B C P).Piece) : Stamp V (Config G n) :=
    ⟨∑ i∈p.val, strand B C P i, fun U => (mill B C P).embers (flags P.threshold U) (Sum.elim (fun i => (B.d i).ink U)
          (heat fun i => (screws B C P i).stamp.ink U)) p⟩

def viewK (P : BudgetPoint) (L : Pack n) (t : Grade V) (U : Config G n) :=
    sliceSum (fun i => (glaze B C P i).name) (fun i => if (mill B C P).remap i = L then
      (glaze B C P i).ink U else 0) t
end Restock

/- Explicit price deck. Inside **this** step.
   `inner` is used on forced+omission+attachment before merger. first-system
    u uses `inner+7` before log (6 for reanchoring/hits, 1 at log tree),
    output needs `radius`. All with the actual `P.B`; after pricing a
    producer must apply contraction/projection INTO this stronger exponent,
    not consume 8 units of output exponent per step. -/
namespace Rates

def radius (P : BudgetPoint) := P.supportExponent+2
def inner (P : BudgetPoint) := radius P + 1
def window (P : BudgetPoint) := (64 * siteUnit P.B)⁻¹
def raw (P : BudgetPoint) := window P / (1 + logPrice P)
end Rates

section
variable (A : Set (V→ℂ))

/-- Only asks ordinary local *first-system* estimates after exact physical
integration, and on flag discrepancy/singleton moves. `f` may vary per
point on admissible parameter domain. -/
structure Supported (B : Brush V G n) (C : Restock V G n) (P : BudgetPoint) (L : V → Support n → Prop) (T : Finset V) : Prop where
  reg i : P.Regular (B.u i).zone (B.u i).stamp.ink
  stamp i : Legible P (B.pack i) (B.d i).ink
  wraps i : P.Regular (C.wrap i).zone (C.wrap i).stamp.ink
  seals i : Spanned P (C.sticker i).zone (C.sticker i).stamp.ink
  att i (U : Config G n) : (C.sticker i).stamp.ink U ≠ 0 → ¬ Healthy P.threshold (C.sticker i).zone U
  inputs i x : x ∈ (B.u i).stamp.name.support → L x (B.u i).zone
  source i x : x ∈ (B.d i).name.support → L x (B.pack i).zone
  clicks i x : x ∈ (C.wrap i).stamp.name.support → L x (C.wrap i).zone
  tags i x : x ∈ (C.sticker i).stamp.name.support → L x (C.sticker i).zone
  free i : i ∉ T → B.pay i = 0 ∧ C.outgoing i = 0
  shape i : along T (C.wrap i).stamp.name ∨ ((C.wrap i).stamp.name = 0 ∧ (C.wrap i).stamp.ink = 0)
  narrow i : along T (C.sticker i).stamp.name ∨ (C.sticker i).stamp.name = 0

variable [Fintype V]

structure Quoted (B : Brush V G n) (C : Restock V G n) (P : BudgetPoint) (κ : ℝ) (z : V → ℂ) : Prop where
  first : ∃ f : ℕ → ℝ, (∀ i, P.supBounds (B.u i).anchor (B.u i).zone ((B.u i).stamp.tell z) (f i)) ∧
      Ac.Hit (fun i => (B.u i).zone) P.B f (Rates.inner P+7) (Rates.raw P)
  extra : ∃ f : ℕ → ℝ, (∀ i, 0 ≤ f i ∧ ∀ x∈(C.wrap i).zone, P.supBounds x (C.wrap i).zone ((C.wrap i).stamp.tell z) (f i)) ∧
      Ac.Hit (fun i => (C.wrap i).zone) P.B f (Rates.radius P) (Rates.window P)
  forced : ∃ f : ℕ → ℝ, (∀ i, ∀ U, ‖(B.d i).tell z U‖ ≤ f i) ∧
      Ac.Hit (fun i => (B.pack i).zone) P.B f (Rates.inner P) (κ * Rates.window P)
  edits : ∃ f : ℕ → ℝ, (∀ i, ∀ U, ‖(C.sticker i).stamp.tell z U‖ ≤ f i) ∧
      Ac.Hit (fun i => (C.sticker i).zone) P.B f (Rates.inner P) (Rates.window P)
end

open Restock

-- calibration equalities about degrees zero and one only

def showBulk {I : Type} (F : I → SmoothLetter V G n) (P : BudgetPoint) (q : Grade V) (U : Config G n) :=
    sliceSum (fun i => (F i).stamp.name) (fun i => masked P.threshold (F i).zone (F i).stamp.ink U) q

def showSeal (F : ℕ → HardLetter V G n) (q : Grade V) (U : Config G n) :=
    sliceSum (fun i => (F i).stamp.name) (fun i => (F i).stamp.ink U) q

/-- Exact unmarked and linear-only producer agreements at the reference port.
    No estimates on a marked/higher output representation here. Still required, in particular
    if reference reset was done iteratively; check on actual packed letters. -/
structure Settled (B : Brush V G n) (C : Restock V G n) (P : Rep G n) (T : Finset V) (w : V → Pulse G n) : Prop where
  funding U : B.base U * Complex.exp (showBulk B.chapter P.p 0 U) =
      (Real.exp (P.exponent U) : ℂ)*Complex.exp (showSeal C.sticker 0 U)
  floorK q U : viewK B C P.p q 0 U=incumbent P U q
  relevant i : i ∈ T → ∀ U, B.pay i+showBulk B.chapter P.p (spike i) U=
      C.outgoing i+showBulk C.wrap P.p (spike i) U+showSeal C.sticker (spike i) U
  amount i : i∈T → ∀ U,C.outgoing i+showBulk C.wrap P.p (spike i) U=(w i).1 U
  freshK i : i∈T → ∀ q U,viewK B C P.p q (spike i) U=(w i).2 q U
end YM.Multi.Vacuum
