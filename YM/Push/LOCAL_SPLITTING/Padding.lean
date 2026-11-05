import YM.Push.LOCAL_SPLITTING.Merge

/-!
# Dormant forced addresses

A sufficient alphabet reservation (can be used abstractly on the actual
history; no transformation then). Also a way to supply it given any activities
at the level of `Rep.Lawful`, its evaluation, and `History.Selected`, by
embedding all the old labels ONCE. Applying that construction gives a modified
history with more labels; not to be applied unilaterally in the middle of
other calculations! Whether used in `Calibrated`, etc., *there* construct and
retain such receipts on the common choice, meeting any stronger requirements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Lattice Wilson RG Source
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side}

abbrev Dummy (n : Side) := {q : Support n × Support n // q.2.Nonempty ∧ q.2 ⊆ q.1} × ℕ

/-- Available even if other labels (including uses at the reserved
addresses themselves) have vacuum and/or source coefficients. We only add
a singleton contribution. Not empty or single-use support assumptions.
No dependency on the eventual stencil/problem choosing how to encode.
-/
structure Reserve (A : Activities G n) where
  code : Dummy n ↪ ℕ
  support (s) : patch A (code s) = s.1.val.1
  inventory (s) : flagsFor A (code s) = s.1.val.2
  allows (s) (U : Config G n) : (A.forced (code s)).extraTest U

variable {A : Activities G n}

def Reserve.slots (R : Reserve A) {ι : Type*} [Countable ι] (X : ι → Support n) : Slots A X := by
  classical
  letI := Classical.choice (nonempty_encodable (Letters A X))
  let e (s : Letters A X) : Dummy n := (⟨(s.total,s.keeps),s.keeps_ne,s.keeps_sub⟩,Encodable.encode s)
  let f : Letters A X ↪ Dummy n := ⟨e,fun a b h => Encodable.encode_injective (congr_arg Prod.snd h)⟩
  exact ⟨f.trans R.code,fun s => R.support _,fun s => R.inventory _,fun s => R.allows _⟩

/-- Version needing no coordination between different callers using independent
slots (merges add linearly). If permutation of actual new addresses rather than
just coordinates/total density is needed, coordinate the `Slots` instead of
making separate calls to this. -/
def slots {ι : Type*} [Countable ι] (h : Nonempty (Reserve A)) (X : ι → Support n) := (Classical.choice h).slots X

namespace Pad

private def letters (n : Side) : ℕ ⊕ Dummy n ≃ ℕ := Classical.choice nonempty_equiv_of_countable

def original (n : Side) : ℕ ↪ ℕ := Embedding.inl.trans (letters n).toEmbedding

def dormant (n : Side) : Dummy n ↪ ℕ := Embedding.inr.trans (letters n).toEmbedding



def blank (s : Dummy n) : ForcedAddress G n := ⟨s.1.val.1,s.1.val.2,s.1.property.1,s.1.property.2,fun _ => True⟩

def add (A : Activities G n) : Activities G n :=
  { A with
    forced := Sum.elim A.forced blank ∘ (letters n).symm
    K := Sum.elim A.K 0 ∘ (letters n).symm
  }

variable (A) in
@[simp] theorem active (i : ℕ) : (add A).forced (original n i) = A.forced i ∧ (add A).K (original n i) = A.K i := by
  simp [original,add]

variable (A) in
@[simp] theorem idle (i : Dummy n) : (add A).forced (dormant n i) = blank i ∧ (add A).K (dormant n i) = 0 := by
  simp [dormant,add]

def reserve (A : Activities G n) : Reserve (add A) where
  code := dormant n
  support s := congr_arg ForcedAddress.support (idle A s).1
  inventory s := congr_arg ForcedAddress.inventory (idle A s).1
  allows s U := (idle A s).1.symm ▸ (show (blank s).extraTest U from trivial)





private def turn (s : Signed) (b : Site n) : Equiv.Perm (Dummy n) := by
  let r := (turnSites s b).finsetCongr
  refine (Equiv.subtypeEquiv (r.prodCongr r) (fun p => ?_)).prodCongr (Equiv.refl _)
  change (p.2.Nonempty ∧ p.2 ⊆ p.1) ↔ (p.2.map _).Nonempty ∧ p.2.map _ ⊆ p.1.map _
  simp











def rep (R : Rep G n) : Rep G n := { R with activities := add R.activities }










end Pad
end YM.Push.Local
