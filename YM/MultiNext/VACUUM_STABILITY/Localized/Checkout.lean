import Mathlib.Algebra.DualNumber
import YM.MultiNext.VACUUM_STABILITY.KThermo
import YM.MultiNext.VACUUM_STABILITY.Localized.Windows


set_option warningAsError false

/-!
# Unmarked and reference check by local partition *before* the log

When propagating the same histories separately for e.g. kernel or reference
ports using other summation protocols. Keep Origins, inventory and stars straight:
`Vetted` at actual flags. These are still contextual inputs at the REAL K-history
on P, all U. Not claiming equivalence to any identities just on `univ`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Windows
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical DualNumber

variable {G : Gauge} {n : Side} {V I : Type}
variable (B : Brush V G n) (C : Restock V G n) (P : BudgetPoint) (U : Config G n)
variable [Fintype V]

omit [Fintype V] in
lemma certified (q : Desk.Grade V) {R : V→Support n→Prop} {T : Finset V} (h : Supported B C P R T) :
    Vetted (flags P.threshold U) (fun i => viewK B C P i q U) := by
  intro i hi; unfold viewK sliceSum; refine (tsum_congr (g:=fun _ => (0:ℂ)) ?_).trans tsum_zero; intro j
  dsimp only; split_ifs with he hb
  · by_contra hx; exact hi (hb ▸ ((glaze_pass h j).inventory U hx))
  all_goals rfl

private abbrev digit := DualNumber ℂ



omit [Fintype V] in
lemma hat_dual (M L : Support n) (F : Pack n→ digit) : TrivSqZeroExt.fst (auditGas L M F) =
    auditGas L M (fun i => (F i).fst) := by
  unfold auditGas; rw [TrivSqZeroExt.fst_sum]; refine Finset.sum_congr rfl fun i hi => ?_
  clear hi
  have ht (i : Pack n) : (tested M Pack.zone F i).fst=tested M Pack.zone (fun i => (F i).fst) i := by unfold tested; split <;> rfl
  induction i using Finset.induction with
  | empty => rfl
  | insert i s hi H =>
    rw [prod_insert hi,prod_insert hi,TrivSqZeroExt.fst_mul,ht,H]

private def Feels (F : ℂ → ℂ) (x : digit) := F 0=x.fst ∧ HasDerivAt F x.snd 0

private lemma turns {F : ℂ → Pack n→ ℂ} {L M : Support n} {g : Pack n→digit}
    (hf : ∀ i,Feels (fun t => F t i) (g i)) : Feels (fun t => auditGas L M (F t)) (auditGas L M g) := by
  have he i : Feels (fun t => tested M Pack.zone (F t) i) (tested M Pack.zone g i) := by
    unfold tested; split
    · exact hf _
    exact ⟨rfl,hasDerivAt_const ..⟩
  have hG (s : Finset (Pack n)) : Feels (fun t => ∏ i∈s,tested M Pack.zone (F t) i) (∏ i∈s,tested M Pack.zone g i) := by
    induction s using Finset.induction with
    | empty =>
      simp only [prod_empty]; exact ⟨rfl,hasDerivAt_const _ _⟩
    | insert i s hi IH =>
      simp only [prod_insert hi]; obtain ⟨ha,hb⟩:= he i; obtain ⟨hc,hh⟩:= IH
      refine ⟨(congrArg₂ _ ha hc).trans (TrivSqZeroExt.fst_mul ..).symm,?_⟩
      have he := hb.mul hh; simp only [ha,hc] at he
      rw [DualNumber.snd_mul,add_comm]; exact he
  unfold auditGas Feels; rw [TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum]; exact
      ⟨sum_congr rfl fun i _ => (hG i).1, HasDerivAt.fun_sum fun i _ => (hG i).2⟩




end YM.Multi.Vacuum.Windows
