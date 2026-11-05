import YM.MultiNext.VACUUM_STABILITY.Words
import YM.Next.EXTRACTION.Tails
import YM.Org.Theatre

set_option warningAsError false

/-!
# Monomial letters for ordinary analytic expansions

Keep the letter even if numerical coefficient or basis entry vanishes. Compare each packed
or rooted sum at vacuum and along singleton axes in THAT algorithm. Finite monomial degree
per letter, unbounded in all the lists.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum
open RG Lattice Wilson Filter Finset Function MeasureTheory Text  Syllable Corona  Desk
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {I J V : Type*} {n : Side} {G : Gauge}

def spike (i : V) : Grade V := Finsupp.single i 1

lemma spike_neq (i : V) : spike i ≠ 0 := by intro h; have he := congrFun (congrArg DFunLike.coe h) i; simp [spike] at he



def along (T : Finset V) (w : Grade V) := ∃ i ∈ T, w = spike i



/-- Keep one exponent medallion on a countable family. -/
def sliceSum (x : I → Grade V) (f : I → ℂ) (q : Grade V) := ∑' i, if x i=q then f i else 0

structure Stamp (V G : Type*) where
  name : Grade V
  ink : G → ℂ

namespace Stamp
variable {A : Type*} (S : Stamp V A)

def say (a : A) : Wave V := MvPolynomial.monomial S.name (S.ink a)

lemma grade (q : Grade V) (a : A) : MvPolynomial.coeff q (S.say a) = if S.name=q then S.ink a else 0 :=
    MvPolynomial.coeff_monomial ..



variable [Fintype V]

def beat (q : Grade V) (z : V → ℂ) := ∏ i : V,(z i)^(q i)

def tell (z : V → ℂ) : A → ℂ := beat S.name z • S.ink

@[simp] lemma tells (z : V → ℂ) (a : A) : S.tell z a = beat S.name z*S.ink a := rfl





@[simp] lemma beat_zero (z : V → ℂ) : beat (0:Grade V) z=1 := by simp [beat]

lemma beat_spike (i : V) (z : V → ℂ) : beat (spike i) z=z i := by simp [beat,spike,Finsupp.single_apply]

lemma beat_add (z : V → ℂ) (w t : Grade V) : beat (w+t) z=beat w z * beat t z := by
  simp_rw [beat,Finsupp.add_apply,pow_add,Finset.prod_mul_distrib]

lemma beat_many (z : V → ℂ) (q : Grade V) (n : ℕ) : beat (n • q) z = beat q z ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul,beat_add z,ih,pow_succ]

lemma beat_list (z : V → ℂ) (x : List I) (q : I → Grade V) : beat (x.map q).sum z = (x.map fun i => beat (q i) z).prod := by
  induction x with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,beat_add,ih,List.prod_cons]

lemma beat_pile (z : V → ℂ) (p : Finset I) (q : I → Grade V) : beat (∑ i∈p,q i) z = ∏ i∈p, beat (q i) z := by
  induction p using Finset.induction with
  | empty => simp
  | insert a l ha ih => rw [sum_insert ha, beat_add,prod_insert ha,ih]



end Stamp

lemma sift {α A : Type*} [NormedAddCommGroup A] [CompleteSpace A] {f : α → A} (hf : Summable f) (P : α → Prop)
    [DecidablePred P] : Summable (fun i => if P i then f i else 0) := by
  refine (hf.indicator (setOf P)).congr fun i => ?_
  by_cases he : P i <;> simp [Set.indicator,he]



section
open Stamp
variable [Fintype V]


end
end YM.Multi.Vacuum
