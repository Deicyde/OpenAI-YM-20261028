import YM.Next.MULTISOURCE.Merger
import YM.Ovens.Coffee



/-!
# Liaison with the other producers

Check that Room *can* propagate through the kind of merger used higher up.
It'd be false to require a slot with extraTest always `True` even after the
Ovens operation. Budget mint from H02 at a stronger support exponent for old
hits (would need to request in application, not an existing production).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Function Filter Finset Pack MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {P : Rep G n}

-- Demanded only for the chosen history, $P.p$ still unchanged.
def reserve (p : BudgetPoint) (r : ℝ) (h : 0 ≤ r) : BudgetPoint :=
  { p with supportExponent:=p.supportExponent+r, exponent_pos:= add_pos_of_pos_of_nonneg p.exponent_pos h }

lemma mint_from {r a : ℝ} (hr : 0 ≤ r) (h : P.activities.KBound (reserve P.p r hr) a) : Mint P r a := by
  obtain ⟨f,hf,hk⟩ := h
  have hp : Summable f := Activities.summable_charge
    (fun i => (P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup)
    (fun i => (hf i).1) hk
  refine ⟨Pack.collect P f,fun i =>
    ⟨tsum_nonneg fun j => (by split; exact (hf j).1; exact le_rfl),fun U =>
      collects_bound P f _ hp (fun i => by rw [Complex.norm_real]; exact (hf i).2 U) _⟩,?_⟩
  let T := P.activities
  intro x; apply le_trans _ (hk x).2.2
  unfold Pack.collect; apply le_of_eq
  simp_rw [← tsum_mul_left]; rw [← Summable.tsum_finsetSum ?_]
  · refine tsum_congr fun i => ?_
    by_cases h : x ∈ (T.forced i).support
    · rw [sum_eq_single (ofAddress T i)]; rotate_left
      · intro b _ hb; rw [if_neg hb.symm, mul_zero]
      · exact fun H => False.elim (H (mem_filter.mpr ⟨mem_univ _,h⟩))
      rw [if_pos rfl, if_pos h]; rfl
    rw [if_neg h]
    refine sum_eq_zero fun j hj => ?_
    rw [if_neg (fun (H : ofAddress P.activities i=j) => h (show x∈ (ofAddress P.activities i).zone from H ▸ (mem_filter.mp hj).2)),mul_zero]
  intro i hi; exact (Pack.access P f hp i).mul_left _

namespace TransferSlots
open Ovens Ovens.Pipes
variable {X : Pipes G n}




end TransferSlots
end YM.Multi
