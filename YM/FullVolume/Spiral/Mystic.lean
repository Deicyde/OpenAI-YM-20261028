import YM.FullVolume.Spiral.Linen
import YM.FullVolume.Spiral.Nilot
/- actual analytic beam compression. prepare File QUIET. `Tail` proof includes every layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c u:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
set_option maxHeartbeats 380000
open Forum
open Extra.Histories.InputColumn
open UniformSpace
-- shared Coil norm. real from complex
section scalar
variable (F Y P)
noncomputable instance : NormedSpace ℝ (Coin F Y P):= NormedSpace.restrictScalars ℝ ℂ (Coin F Y P)
instance : IsScalarTower ℝ ℂ (Coin F Y P):= by constructor; intro x y z; show _=(algebraMap ℝ ℂ x) • y • z; rw [smul_smul]; rfl
end scalar
lemma aspects' (c:ℝ)(f:Coin F Y P): c • f=(c:ℂ) • f:=rfl
-- Saver total
private lemma hookedK (Q: Coefficient F n)(h: Q.Format 0 Y P.orient ∧ ∃ u,Q.remBound 0 P.orient P.k u)(S:Keeper P.orient.p P.orient.activities): Pay F Y P (capture Q S) h.2.choose:=alongPay ⟨⟨rfl,rfl⟩,rfl⟩ S Q h.1 h.2.choose_spec
def alb (y: Coefficient F n)(Y:Hol G)(P:Desk G n)(K:Keeper P.orient.p P.orient.activities): Coin F Y P:= if h:y.Format 0 Y P.orient ∧ ∃ u,y.remBound 0 P.orient P.k u then Coin.saver F Y P (capture y K) (hookedK y h K) else 0
lemma alb_read (y: Coefficient F n)(Y:Hol G)(K:Keeper P.orient.p P.orient.activities)(ht:y.Format 0 Y P.orient)(hx:y.remBound 0 P.orient P.k u):Coin.uses (alb y Y P K)=capture y K:=by unfold alb; rw [dif_pos ⟨ht,_,hx⟩,Coin.use_save] -- add u variable
section wealth
variable (K:Keeper P.orient.p P.orient.activities)
lemma pressed (w:Rung) (h:Stays p) (hP:∀ i,(p i).remBound 0 A_ P.k v): capture (weave w p) K= Jams.mix w (fun i=>capture (p i) K):=by
   let S:=(p tip).support; let k:= tongue S; refine Prod.ext ?_ (funext fun i=>?_)
   · funext j; rw [Jams.mix, Prod.fst_sum, Finset.sum_apply]; change liveE _ j=∑ i∈w.support, (w i) • liveE _ j
     by_cases he:j∈ range k
     · obtain ⟨i,rfl⟩:=he
       have hx(u:sun): liveE (p u) (k i)=(p u).regular i:=by unfold liveE; rw [h u]; exact k.injective.extend_apply ..
       simp_rw [hx]; rw [show liveE (weave w p) (k i)= _ from (show _= (weave w p).regular i from k.injective.extend_apply ..)]
       change Jams.mix w (fun i=>(p i).regular) i= _; rw [mix_apply'];rfl
     have ht(i:sun):liveE (p i) j=0:=by unfold liveE; rw [h i]; exact Function.extend_apply' _ _ _ he
     simp_rw [ht,smul_zero,Finset.sum_const_zero]; exact Function.extend_apply' _ _ _ he
   unfold Jams.mix; rw [Prod.snd_sum,Finset.sum_apply]; change stowK K _ i= ∑ j∈w.support, (w j) • stowK K (p j) i
   by_cases he:i∈ range (cart K)
   · obtain ⟨i,rfl⟩:=he; simp_rw [stowed]; funext V
     unfold profile cram; simp only [weave, Jams.mix, Finset.sum_apply, Pi.smul_apply]; rw [Summable.tsum_finsetSum _ ]; apply Finset.sum_congr rfl; intro i h
     simp [Complex.real_smul,tsum_mul_left]
     intro j _; exact (((rem_dominated (hP j)).summable V).comp_injective Subtype.val_injective).const_smul _
   simp_rw [pit _ _ he,smul_zero,Finset.sum_const_zero]
namespace Forum
variable (h:Forum p q y Y P a b)
include h K
lemma compass : Rebar q (phraseS (fun i:sun=> ((alb (p i) Y P K:Coin F Y P):Completion (Coin F Y P)))) b∧ Rebar q (phraseS (fun i:sun=>(p i).x-y)) a:=by
   have he i:=h.play i; let f(i:sun):Coin F Y P:=alb (p i) Y P K
   have hP(i):Coin.uses (f i)=capture (p i) K:= alb_read (p i) Y K (he i).2.1 (he i).2.2
   refine ⟨⟨h.knows,rem_nonneg (he tip|>.2.2),fun w η ht=>?_⟩,h.knows,(Work.G08.size_nonneg _ _).trans (he tip).1,fun w η ht=> by rw [mix_made]; exact (Size.norm_le F _).trans (h.burns w η ht)⟩
   rw [mix_made,Urns.regs_map_eq, Completion.norm_coe]; apply (Coin.wealths _).mpr
   rw [show Coin.uses (Jams.mix w f)=capture (weave w p) K from ?_]; exact alongPay (show Well A_ P P.k from ⟨⟨rfl,rfl⟩,rfl⟩) K (weave w p) (h.earns w η ht).1 (h.earns w η ht).2
   rw [pressed K w h.stuck (fun i=> (he i).2.2)]; unfold Jams.mix; rw [map_sum]; apply Finset.sum_congr rfl; intro i _
   rw [aspects', map_smul,hP]; apply Prod.ext <;> (funext i U; exact Complex.real_smul.symm)
end Forum
end wealth
end YM.FullVolume.Paint.Tower
