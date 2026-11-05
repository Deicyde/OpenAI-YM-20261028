import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.Nilpotent.Exp
import YM.Next.SCHEDULE.Blocks
import YM.Push.CORRECTED_COLUMNS.Placement
import YM.Push.CORRECTED_COLUMNS.Tree
/-!
# Finite-cell normal ordering convention 

Use ALL partial matchings, one orientation, no new marker random
variables. Works even with coincident color/face slots (orientation
transport done before this) and singular or zero covariances. Real
normal ordering parameter; cost arguments require authentic Cov on the
whole finite torus with the harmonic convention chosen in free comparison,
not a continuum limit. This elementary algebra works for EVERY supplied
matrix.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Loop
open Filter Lattice Wilson RG Source Source.Drops Labels Cells Extraction
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {l : ℕ}

abbrev Pair (l : ℕ) := Fin l × Fin l
abbrev Pairs (l : ℕ) := Finset (Pair l)

def ends (p : Pair l) : Finset (Fin l) := {p.1,p.2}

def closed (A : Pairs l) := A.biUnion ends

def loose (S : Finset (Fin l)) (A : Pairs l) := S \ closed A

def joins (S : Finset (Fin l)) : Finset (Pairs l) := Finset.univ.filter (fun A =>
    (∀ p∈A,p.1 < p.2) ∧ closed A ⊆ S ∧ ∀ p∈A,∀ q∈A,p≠q → Disjoint (ends p) (ends q))



@[simp] lemma empty_in (S : Finset (Fin l)) : ∅∈joins S := by simp [joins,closed]
@[simp] lemma closed_empty : closed (∅:Pairs l)=∅ := by simp [closed]
@[simp] lemma loose_empty (S : Finset (Fin l)) : loose S ∅=S := by simp [loose]









section Formal
variable {R : Type*} [CommRing R]

/-- Linear triangular transform on occurrence-indexed polynomials. -/
def sew (P : Pair l → R) (E : Finset (Fin l) → R) (S : Finset (Fin l)) :=
    ∑ A∈joins S,(∏ a∈A,P a) * E (loose S A)



@[simp] lemma sew_zero (E : Finset (Fin l) → R) (S : Finset (Fin l)) : sew 0 E S = E S := by
  unfold sew; rw [Finset.sum_eq_single_of_mem ∅ (empty_in S)]
  · simp
  intro b _ hb; simp [hb]




end Formal
end YM.Further.CorrectedLift.Loop
