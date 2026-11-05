import Mathlib.RingTheory.Nilpotent.Exp
import YM.Ac.Tree
import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Push.CORRECTED_COLUMNS.Placement


/-!
# Unscaled comparison series, at value order

Part of CORRECTED_SOURCE_MACHINE. Sums (including before/after
reindexing) are over actual occurrences. `sum_parts` in this file lets us
exponentiate a *summable, not necessarily finitely supported*, list of
hot monomial occurrences, without assuming finite-volume absolute estimates
are usable uniformly. Prices refer to the whole polynomial in the specified
`Census`. We will use this both for negative marked log occurrences on the
restart, and for mask movements on marked activities.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Lattice Wilson RG Marker Function Set Filter Overlay
open Push.Corrected 
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {V : Type*} [DecidableEq V] {R : Census V}
variable {α β : Type*}







lemma hit_summable {n : Side} {M : ℕ} {a b : ℝ} {Y : α → Support n} {g : α → ℝ}
    (ha : 0 ≤ a) (hp : ∀ i, 0 ≤ g i) (h : Ac.Hit Y M g a b) (hY : ∀ i, (Y i).Nonempty) :
    Summable g := by
  let b (x : Site n) i := if x ∈ Y i then g i*Real.exp (a*coverNumber M (Y i)) else 0
  have hb := summable_sum (s:=Finset.univ) (f:=b) (fun x _ => (h x).2.1)
  refine hb.of_nonneg_of_le hp (fun i => ?_)
  obtain ⟨x,hx⟩ := hY i
  calc
    _ ≤ g i * Real.exp (a*coverNumber M (Y i)) := le_mul_of_one_le_right (hp _) (Real.one_le_exp (by positivity))
    _ = b x i := by simp only [b,if_pos hx]
    _ ≤ ∑ j,b j i := Finset.single_le_sum (fun j _ => (h j).1 i) (Finset.mem_univ x)

end YM.Further.ThresholdSourceRestart
