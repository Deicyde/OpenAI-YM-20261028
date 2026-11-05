import YM.RemainderComparison.Flues.Yard
import YM.Work.H03

/-!
# Expanded labels still read the corresponding support budgets
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Flues
open Function Filter Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums Finset Merge Work.H03
open Mosaic Mosaic.Verse Marker
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n : Side} {ι θ : Type}[DecidableEq θ] {α:Type*} {J : Census θ}
variable (H:Yard ι α G n) (L:Scone ι α G n) (P:BudgetPoint) (root:ι→Support n)(Z:Set ι)(k:ℕ)
local notation "C" => fireplace H L
variable (F:ℕ ≃ (fireplace H L).Pellet)
local notation "D" => flash H L P Z F
variable (h:H.Sounds P root)(hl:L.Rises P root)
include h
lemma finds (a : α) (i:ℕ) : UsesFinal P.threshold ((addr F P i).support) ((addr F P i).extraTest) ∧
      (∀ k U,(addr F P i).extraTest (gauge k U) ↔ (addr F P i).extraTest U)∧ MeasurableSet {U| (addr F P i).extraTest U}:=by
   let f:= (F i).val.toLeft
   let l(j):= (H.more j).eligible P.threshold
   have hz j k V: l j (gauge k V)↔l j V:= eligible_gauge _ _ _ _ ((h.families a).symtest j k V)
   have hs j (hj:j∈f) : UsesFinal P.threshold ((addr F P i).support) (l j):=
      reads_larger (subset_biUnion_of_mem (C).patch (mem_toLeft.mp hj)) (eligible_reads _ _ ((h.families a).reads_test j))
   change UsesFinal _ _ (condition F P i)∧ (∀ k U, (∀ j∈ f, l j (gauge k U))↔ (∀ j∈f,l j U))∧MeasurableSet {U|∀ j∈f,l j U}
   refine ⟨?_,fun k U=> by simp_rw [hz],?_⟩
   · intro U V hp hv; exact propext ⟨fun H j hj=>(hs j hj U V hp hv).mp (H j hj), fun H j hj=> (hs j hj U V hp hv).mpr (H j hj)⟩
   rw [Set.setOf_forall]; apply MeasurableSet.iInter; intro i
   by_cases hi:i∈f
   · simp only [hi,true_imp_iff]; exact eligible_measurable _ _ ((h.families a).meas_test i)
   simp [hi]
include hl
lemma attracts (a:α)(i:Ovens.Label) : UsesFinal P.threshold ((C).patch i) (stoke H L Z a i)∧
      GaugeInvariant (stoke H L Z a i)∧ Measurable (stoke H L Z a i)∧ apex root ((C).patch i) (rune H L i) (stoke H L Z a i):=by
  rcases i with i|i
  · exact ⟨(h.families a).reads i,(h.families a).sym i,(h.families a).meas i,h.invested i a⟩
  have hx i₁ hi V hv := hl.origin i a i₁ hi V hv
  refine ⟨?_,?_,?_,fun i₁ hi V hv=>hx i₁ hi V fun h=> hv (L.ashes Z h)⟩
  · intro U V hp ht; change Scone.tinct L Z a i U= Scone.tinct L Z a i V; unfold Scone.tinct; rw [hl.reads a i U V hp ht]
  · intro k V; change Scone.tinct L Z a i _= Scone.tinct L Z a i _; unfold Scone.tinct; rw [hl.durable a i k V]
  change Measurable (L.tinct Z a i)
  by_cases hz: load Z (L.glyph i)=0
  · unfold Scone.tinct; simp_rw [if_pos hz]; exact (Real.measurable_exp.comp (hl.borel ..)).sub measurable_const
  unfold Scone.tinct; simp_rw [if_neg hz]; exact hl.borel ..
lemma flash_sound : (flash H L P Z F).Sounds P root:=by
  let f (a:α) i (V:Config G n):= ∏ j∈(F i).val,stoke H L Z a j V
  have hm i j (hj:j∈ (F i).val): (C).patch j ⊆ (addr F P i).support:= subset_biUnion_of_mem _ hj
  have hz(a i): UsesFinal P.threshold ((addr F P i).support) (f a i):=fun U V hp hf=> prod_congr rfl fun j hj=> reads_larger (hm i j hj) (attracts H L P root Z h hl a j).1 U V hp hf
  have hx a i: GaugeInvariant (f a i) := fun k U=> prod_congr rfl fun j _=> (attracts H L P root Z h hl a j).2.1 k U
  have ht a i: Measurable (f a i):= measurable_fun_prod _ fun j _=> (attracts H L P root Z h hl a j).2.2.1
  constructor
  · intro a; have H' i:= finds H L P root F h a i; refine ⟨?_,fun i=>(H' i).2.1, fun i=> Measurable.ite (eligible_measurable _ _ ((H' i).2.2)) (ht a i) measurable_const,fun i=>(H' i).2.2, ?_,fun i=> (H' i).1, fun i U hn=> Classical.byContradiction fun hh=> hn (if_neg hh)⟩
    · intro i k V; change (if (addr F P i).eligible P.threshold _ then f a i (gauge k V) else 0)=(if (addr F P i).eligible P.threshold V then f a i V else 0); rw [show (addr F P i).eligible P.threshold (gauge k V) = _ from propext (eligible_gauge _ _ _ _ ((H' i).2.1 k V)), hx a i k V]
    intro i U V hp hf; change (if (addr F P i).eligible P.threshold U then f a i U else 0)=(if (addr F P i).eligible P.threshold V then f a i V else 0); rw [eligible_reads _ _ (H' i).1 U V hp hf,hz a i U V hp hf]
  intro i a j hj V hn
  obtain ⟨z,hz,hj⟩:= (Mosaic.holds (F i).val (rune H L) j).mp hj
  refine ((attracts H L P root Z h hl a z).2.2.2 j hj V (fun he=>hn ?_)).trans (hm i z hz)
  unfold flash; dsimp only; split; exact prod_eq_zero hz he; rfl
end YM.RemainderComparison.Flues
