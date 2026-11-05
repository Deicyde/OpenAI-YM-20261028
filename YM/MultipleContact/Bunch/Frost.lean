import YM.MergeProof.North.Jazz
import YM.MergeProof.North.Wiring
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Wiring

/- generalized from YM.MergeProof.North.Frost to arbitrary arity -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories Float
open scoped Topology BigOperators Classical
variable {V I : Type}[Fintype V][DecidableEq V][Fintype I]{B:Census V} {G:Gauge}{n:Side}{R:Rep G n}{v:V}{t a x b: ℝ}{w:V→ℝ}
lemma pinch (i:V){o : V→Site n}{X:I→Support n}{P:BudgetPoint}{F:I→ Config G n→ Poly B} (hq:∀ i,Borne o (X i) (F i) P.threshold) (hr:Towed w X F P.B P.supportExponent a)(hw:∀ i,0<w i):∃ f:I→ℝ, (∀ j U, ‖(F j U).part (B.fire i)‖ ≤ f j)∧ ∑ j,P.mass (X j) (f j) ≤ a/w i:=by
    -- individual summed. Need Fintype V for diced?
    obtain ⟨x,hh,hX,hV⟩:= Salt.diced F X w P.supportExponent a P.B hw hr
    let f j:= if o i∈ X j then x (j,B.fire i) else 0
    refine ⟨f,fun j U=>?_, (le_div_iff₀ (hw i)).mpr ?_⟩
    · unfold f; split; next=> exact hX (j,B.fire i) U
      next hz=> rw [show (F j U).part (B.fire i)=0 from ?_,norm_zero]; exact Classical.byContradiction fun h=> hz ((hq j).place _ U h (mem_image_of_mem _ (show i∈ (B.fire i).val from mem_singleton_self _)))
    have ht:= hV (o i); let g(j):=P.mass (X j) (f j)*w i
    have hp := Budget.pull_le (q:=fun j:I=>(j,B.fire i)) (p:=fun _=>True) ht (?_ : ∀ j,0≤g j) (fun _ _=> trivial) (show Set.InjOn _ _ from (show Function.Injective (fun j:I=>(j,B.fire i)) from fun _ _ h => Prod.mk.inj h|>.1).injOn) ?_
    · rw [Finset.sum_mul]; exact Budget.cap hp univ
    · intro j; apply mul_nonneg _ (hw i).le; apply mul_nonneg (Real.exp_pos _).le; unfold f;split;exact hh _;rfl
    intro i _; unfold g; apply le_of_eq; unfold BudgetPoint.mass f; dsimp only [Function.comp_apply]; split_ifs; rw [Poly.solo_toll]; ring
    ring
variable {o:V→Site n} {F : Support n→ Config G n→Poly B}{K:Box n→ Config G n→Poly B}
lemma sprouts (v:V)(A:Menu.Arsenal R)(hF:∀ i,Burns o i (F i) R.p.threshold)(hK:∀ i,Flow o i (K i) R.p.threshold)(ht:Towed w id F R.p.B R.p.supportExponent a)(hh:Towed w Prod.fst K R.p.B R.p.supportExponent b)(hw:∀ i,0<w i): Blade R (o v) (fun U=>(∑ i,F i U).part (B.fire v)) (fun j U=>(K j U).part (B.fire v)) 0 (2*(a/w v)+2*(b/w v)):=by
    let f i U:= (F i U).part (B.fire v); let g i U:= (K i U).part (B.fire v)
    obtain ⟨x,hx,hT⟩:=pinch v (fun i=> (hF i).toBorne) ht hw; obtain ⟨y,hy,hJ⟩:=pinch v (fun i=>(hK i).toBorne) hh hw
    have hv : (fun U=>(∑ i,F i U).part (B.fire v))=∑ i,f i:=by funext i; rw [Finset.sum_apply,Poly.part_sum]
    have he(i:Support n): Blade R (o v) (f i) 0 0 (2*R.p.mass i (x i)) := by
       let h:= hF i|>.toBorne
       apply Float.petals A _ _ (fun k U=> congr_arg (fun f=>Poly.part f (B.fire v)) (h.turns k U)) (h.me _) (fun U V he ht=>congr_arg (fun f=>Poly.part f (B.fire v)) (h.home _ _ he ht)) (fun U H=> (hF i).permits U (fun hi=>H (by rw [hi];rfl))) (fun hh=>?_) (hx i)
       obtain ⟨U,hU⟩:= Function.ne_iff.mp hh; apply h.place (B.fire v) U hU; exact mem_image_of_mem _ (mem_singleton_self v)
    have hp(i:Box n): Blade R (o v) 0 (Pi.single i (g i)) 0 (2*R.p.mass i.1 (y i)):=by
       let h:= hK i|>.toBorne
       apply Float.pillars A i _ (fun k U=>congr_arg (fun f=>Poly.part f (B.fire v)) (h.turns k U)) (h.me _) (fun U V he ht=> congr_arg (fun f=>Poly.part f (B.fire v)) (h.home U V he ht)) (fun U H=> (hK i).permits U (fun hi=>H (by rw [hi]; rfl))) (fun hh=>?_) (hy i)
       obtain ⟨U,hU⟩:= Function.ne_iff.mp hh; apply h.place (B.fire v) U hU; exact mem_image_of_mem _ (mem_singleton_self v)
    have ht:= (comp_many f _ _ _ Finset.univ (fun i _=> he i)).comp (comp_many _ _ _ _ Finset.univ (fun i _=>hp i))
    simp only [sum_const_zero,add_zero,Float.supple g,zero_add, ← Finset.mul_sum] at ht
    rw [hv]; exact ht.more (add_le_add (mul_le_mul_of_nonneg_left hT zero_le_two) (mul_le_mul_of_nonneg_left hJ zero_le_two))
-- selecting accounts
lemma socket {f:Config G n→ℂ}{K:Res G n}{o:Site n}{z:ℂ}(h: Blade R o f K z a): ∃ k:ℕ→ Config G n→ℂ, Dominated k∧ profile R.activities k=K:=by
    obtain ⟨I,i,M,s,h⟩:=h; let K'(i):= s i • line (M i); have ht i:Dominated (K' i):=rainbow (linemark _) _
    refine ⟨∑ i,K' i,combies K' ht _,?_⟩; rw [prof_sum K' ht,h.run]; simp_rw [K',profile_scale,banner]
end YM.MergeProof.BatchRibbons
