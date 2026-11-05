import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Emitter
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Equivalence

set_option warningAsError false

/-!
# All-channel movement for the restored Activities
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Rename
open Lattice RG Wilson Finset Filter Function Relation
open Emit Restore  AbsoluteSums AbsoluteSums.Ursell Attach
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {ι κ : Type*} {n : Side} {G : Gauge}




section Axis
variable (X : ι → Support n) (Y I : κ → Support n) (u : Config G n → ι → ℝ)
    (d : Config G n → κ → ℝ) (v : Clusters ι → ℝ) (test : κ → Config G n → Prop) (s : Signed) (b : Site n)

/-- For a translation/signed turn. Maps must work on whole alphabets.
We include v clause in case choosing offsets not from the identity (when
choosing v from the identity, follows by label transformation; see below).
-/
structure Turn where
  q : Equiv.Perm ι
  j : Equiv.Perm κ
  locF i : X (q i) = send (StepData.sendSites s b) (X i)
  locK i : Y (j i) = send (StepData.sendSites s b) (Y i)
  invt i : I (j i) = send (StepData.sendSites s b) (I i)
  probF i V : u V (q i) = u (pull s b V) i
  probK i V : d V (j i) = d (pull s b V) i
  probC i : v (tuple q i)=v i
  tests i V : test (j i) V ↔ test i (pull s b V)



namespace Turn
variable {X Y I u d v test s b} (E : Turn X Y I u d v test s b)

def a : Equiv.Perm (Site n) := StepData.sendSites s b -- E binder not included







-- Names left/right retain the original memberships. Use even for
-- earlier predicates that must still be checked *before* stamping the
-- new forced coverage.
















section Output

private def shiftLeaf (i : Clusters ι) : ↥(X (i.snd none)) ≃ ↥(X ((tuple E.q i).snd none)) :=
  Equiv.subtypeEquiv (a (s:=s) (b:=b)) (show ∀ x : Site n, x∈X (i.snd none) ↔ _ from fun i' => by
    change i'∈_ ↔ _ ∈ X (E.q (i.2 none)); rw [E.locF,show a (s:=s) (b:=b)= _ from rfl]; exact (listed ..).symm)

private def anchors (i : Anchors X) : Anchors X := ⟨tuple E.q i.1,shiftLeaf E i.1 i.2⟩

def anchorMap : Equiv.Perm (Anchors X) := by
  apply Equiv.ofBijective (anchors E)
  constructor
  · rintro ⟨x,y⟩ ⟨t,v⟩ h
    have he : x=t := (tuple E.q).injective (congr_arg Sigma.fst h)
    subst t
    have hp : y=v := (shiftLeaf E x).injective (eq_of_heq (Sigma.mk.inj h).2)
    subst v; rfl
  rintro ⟨x,y⟩
  obtain ⟨t,rfl⟩ := (tuple E.q).surjective x
  obtain ⟨u,rfl⟩ := (shiftLeaf E t).surjective y
  exact ⟨⟨t,u⟩,rfl⟩










variable (hI : ∀ i,(I i).Nonempty) (hQ : ∀ i,I i⊆Y i) (p : BudgetPoint)



variable [Countable ι] [Countable κ]


end Output
end Turn
end Axis
end YM.Push.LogIdentity.Rename
