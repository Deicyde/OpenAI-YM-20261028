import YM.FullVolume.Shroud.Seeds
import YM.SectorNext.VACUUM_NORMALIZATION.Covered
import YM.Next.WARD_BIN.Spin
import YM.Push.LOCAL_SPLITTING.Direct
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Shroud
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Source Labels Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Next.Foundations Push Precision WilsonStartup
open UVNext.CouplingReset UVNext.PricedKernels Ovens Ovens.Pipes Progress.DirectedRecipe BudgetPoint Extra.Iteration
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side} {P:BudgetPoint}{D:PathData G}{c:Clip}{σ C Λ b w:ℝ}
namespace Well
open Push.BetaTransport SectorNext.Vacuum
lemma wit {k:PathData G}{σ u v}(c:Clip)(h:k.Bounds c σ u v)(x:ℝ)(P:BudgetPoint)(U:Config G n) (F: Face (Per n)):
    ‖k.ell U F‖≤u*2:=by
    let p i:=k.ellTerms F i U; have hp:SumBudget (fun i=>‖p i‖) (u*2):=by
       let a i:=|((k.row F.2 i).1)| * Real.exp (σ*(k.row F.2 i).2.length); have hf:= Extra.Multi.Budget.scale (h.rows F.2) zero_le_two
       apply Extra.Multi.Budget.mono hf (fun _ => norm_nonneg _) (fun i=>?_ ) (mul_comm ..|>.le)
       unfold p PathData.ellTerms; rw [norm_smul,Real.norm_eq_abs,mul_comm (2:ℝ)]; exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (Nat.cast_nonneg _)))) (Slot.eval_norm ..) (norm_nonneg _) (by positivity)
    exact (norm_tsum_le_tsum_norm hp.2.1).trans hp.2.2
lemma gasoline (P:BudgetPoint) (c:Clip)(σ C Λ:ℝ)(n:Side) :∃ b:ℝ,0 ≤ b ∧ ∀ R : PathData G,R.Bounds c σ C Λ → ∀ U:Config G n, ‖kinetic R c P U‖≤b:=by
    let v:= c.direct * 2^2/2+c.linear*P.threshold*2; let x:= v+(C*2)^2/2
    let y:=Fintype.card (Face (Per n)) * x+Fintype.card (Site n)*(C*P.threshold^3+C*P.threshold^4)
    refine ⟨max y 0,le_max_right ..,fun R h U=> ?_⟩
    have hf(V:Config G n) (i: Face (Per n)): |R.baseTerm c P V i|≤x:=by
        rw [abs_of_nonneg (R.base_nonneg ..)]; unfold PathData.baseTerm; refine add_le_add ?_ ?_
        · have hh:= G.chord_nonneg (faceValue V i); have hv:= G.chord_le_two (faceValue V i); have hk:= P.threshold_pos; have hc:= c.tail_pos; have hp:=c.quadratic_pos
          unfold PathData.clipped; split; next=> exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh hv _) hp.le) zero_le_two).trans (le_add_of_nonneg_right (by positivity))
          next=> exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans (le_add_of_nonneg_left (by positivity))
        split; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (wit c h 0 P V i) _) zero_le_two; positivity
    have ht(V:Config G n)(x:Site n):|PathData.atomSeries R.cubic P V x+PathData.atomSeries R.quartic P V x|≤ C*P.threshold^3+C*P.threshold^4:=(abs_add_le ..).trans (add_le_add (atomVolume _ _ _ _ h.width h.three) (atomVolume _ _ _ _ h.width h.four))
    let T (V:Config G n):= (∑ i,R.baseTerm c P V i)+∑ i: Site n,(PathData.atomSeries R.cubic P V i+PathData.atomSeries R.quartic P V i); have hy(V:Config G n) : |T V| ≤ y:=by
        unfold T; refine (abs_add_le ..).trans (add_le_add ((abs_sum_le_sum_abs ..).trans ?_) ((abs_sum_le_sum_abs ..).trans ?_))
        · simpa only [sum_const, Finset.card_univ, nsmul_eq_mul] using (Finset.sum_le_sum (s:=Finset.univ) (g:=fun _=>x) fun i _=> hf V i)
        simpa only [sum_const,Finset.card_univ,nsmul_eq_mul] using (Finset.sum_le_sum (s:=Finset.univ) (g:=fun _=>_) fun i _=> ht V i) -- v implicit
    apply le_trans _ (le_max_left ..); change |VerifiedReset.factor * ∑ i:Signed,T (pull i 0 U)|≤ y
    rw [abs_mul,abs_of_pos factor_pos]; refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=>hy _)) factor_pos.le|>.trans_eq ?_
    simp only [sum_const, Finset.card_univ,nsmul_eq_mul,← mul_assoc,factor_card,one_mul]
-- prefer have Struct U.Work.Impt.No nonsmall Δ requirements.
variable {R: Rep G n}(h:R.Lawful σ C Λ b w)
abbrev leg (R:Rep G n)(U:Config G n):= kinetic R.path R.clip R.p U
lemma mirrors (t:Signed)(x:Site n)(U:Config G n): leg R (pull t x U)=leg R U:=by
    have hp:=Push.Local.channels_pull R.path x R.clip R.p t U 1
    have hf:= Push.Local.channels_pull R.path x R.clip R.p t U 0
    rw [channels_split _ 1,channels_split _ 1,hf] at hp; simpa only [one_mul,add_right_cancel_iff] using hp
include h
lemma axial : GaugeInvariant (leg R):=by
    let V:={R with beta:=0}; let P:={R with beta:=1}; have hv:V.Lawful σ C Λ b w:=⟨h.paths,h.labels⟩; have hp:P.Lawful σ C Λ b w:=⟨h.paths,h.labels⟩ -- not defeq Lawful but constructor
    have hm(U): V.exponent U-P.exponent U= leg R U:=by dsimp only [V,P,Rep.exponent]; rw [channels_split (b:=1) U]; unfold leg; ring
    intro t U; rw [← hm,← hm,Push.Local.Kernel.exp_invariant hp,Push.Local.Kernel.exp_invariant hv]
lemma oiled : GaugeInvariant (R.activities.gas R.p):=by
    intro t U; unfold Activities.gas; apply tsum_congr; intro i; simp only [Activities.gasOccurrence,Activities.admissible, gauge_flags]; simp_rw [h.labels.forced.sym _ t U]; congr!
omit h
lemma defended (t:Signed)(x:Site n)(hp:R.activities.Moves t x)(U:Config G n): R.activities.gas R.p (pull t x U)=R.activities.gas R.p U:=by
    have ht:= Push.Local.eval_pull hp U; unfold Rep.eval at ht; rw [Push.Local.exponent_pull hp] at ht; exact mul_left_cancel₀ (Real.exp_ne_zero _) ht
end Well
end YM.FullVolume.Shroud
#print axioms YM.FullVolume.Shroud.Well.axial
#print axioms YM.FullVolume.Shroud.Well.defended
#print axioms YM.FullVolume.Shroud.Well.gasoline
#print axioms YM.FullVolume.Shroud.Well.oiled
