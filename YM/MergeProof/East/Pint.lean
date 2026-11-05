import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Awaken
import YM.MergeProof.East.Ladle
import YM.MergeProof.East.Plume

/-!
# Station.real. Probes without limits in p and N along a single row
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p:ℕ} {ι:Type} {b z:ℝ}
variable {P:ι → Tapes.Panel D} {B:Binding C}{H:C.Makes}{O:HaarBudget G}{J:ChartRatio G}
local notation "A" => C.path.levels
local notation "S"=> standard C
variable {L:ℕ→ℕ→TableL C D}
open Analysis Next.UVStress
variable (aux:ℝ)
def wok (C:Family G)(D k:ℕ)(b ξ:ℝ)(L:ℕ→ℕ→TableL C D): Wheel C D := {
   r:=gap C.path.levels b k
   rad:=gap_pos ..
   atCut:= fun x d=>((ladd C (Station.mag C.path.levels b k) k x.1 x.2 d (L x.1 x.2 d)).toContinuousLinearMap).comp (ladder C d)
   grid:=k
   σ:=Perch.bill ξ (clim C.path.levels k)
   stripe:=Real.exp_pos _ }
lemma wok_spacing : (wok C D k b aux L).spacing=(Station.mag A b k)⁻¹ :=by
   change C.S.a k/(gap _ _ k)=_; unfold Station.gap;rw [div_eq_mul_inv,mul_inv_rev,mul_left_comm,mul_inv_cancel₀ (C.S.a_pos k).ne',mul_one]
open Climb Ward
private lemma many_clm {E V:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E][NormedAddCommGroup V][NormedSpace ℂ V]
    {ι:Type*}(P:ι→Prop)(T:ι→ E →L[ℂ] V)(h:∀ x:E,∃ K :ℝ,∀ i,P i→‖T i x‖≤K):∃ K:ℝ,0 ≤ K∧∀ i,P i→‖T i‖ ≤ K:=by
   let B:= Module.finBasis ℂ E
   choose K hA using fun i : Fin (Module.finrank ℂ E)=> h (B i)
   let D (i):= (B.coord i).toContinuousLinearMap
   let c:=∑ i:Fin _,‖D i‖*|K i|; have hc : 0≤c:= Finset.sum_nonneg fun _ _=> by positivity
   refine ⟨c,hc,fun i hi=> ContinuousLinearMap.opNorm_le_bound _ hc (fun x=>?_ )⟩
   conv_lhs=> rw [← B.sum_repr x]; rw [map_sum]
   apply (norm_sum_le ..).trans; dsimp only [c]; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun j _=>?_
   rw [map_smul,norm_smul]; refine (mul_le_mul (show ‖B.repr x j‖ ≤ ‖D j‖ * ‖x‖ from (D j).le_opNorm x) ((hA j i hi).trans (le_abs_self _)) (norm_nonneg _) (by positivity)).trans_eq ?_;ring
include H
lemma w_right (F:Extraction.Order)(h: (S).RealSpin)(b:ℝ)(hp:Poised P B H O J n z k L) :
    let Y:=wok C D k b aux L
    (∃ M:ℝ,F.late fun N p=> ‖Y.atCut (N,p)‖ ≤ M)∧F.late fun N p=>
       Y.atCut (N,p) ⟨0,Nat.succ_pos D⟩ ((S).unit 0)= C.book.scalar 0 ∧
       (∀ i x,Y.atCut (N,p) i ((S).conj h i x)=star (Y.atCut (N,p) i x))∧
       ∀ i s x,Y.atCut (N,p) i ((S).mirror h i s x)=C.book.mirrorGroup i s (Y.atCut (N,p) i x) :=by
    intro Y
    have he(i:Fin (D+1)): C.ref i ≤ k :=hp.early _ (Nat.le_of_lt_succ i.isLt)
    let μ:= Next.Rank.Station.mag A b k
    have hh(i:Fin (D+1)) (x) :∃ M:ℝ,∀ l:ℕ×ℕ,k<l.1 → ‖Y.atCut l i x‖≤M:=by
       obtain ⟨w,hw⟩:= sun H (he i) μ (ladder C i x); refine ⟨w,fun l hl=>?_⟩; exact hw _ _ _ hl.le (hp.charts l.1 l.2 hl i).1
    choose S' ht ht' using fun i:Fin (D+1)=> many_clm (fun l:ℕ×ℕ=>k<l.1) (fun l=> Y.atCut l i) (hh i)
    have hz:F.late fun N _=>k<N:= by unfold Extraction.Order.late; exact Eventually.of_forall fun i=> F.mesh.cofinal.eventually (eventually_gt_atTop _)
    refine ⟨⟨∑ i,S' i,hz.mono fun i he=>he.mono fun j h=> (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _=> ht i)).2 fun y=> (ht' y (F.mesh j,F.per i) h).trans (Finset.single_le_sum (fun i _=>ht i) (Finset.mem_univ _))⟩,?_⟩
    refine hz.mono fun i he'=>he'.mono fun j hk=> ?_
    let K:=F.mesh j; let β:= F.per i
    let d0:Fin (D+1):=⟨0,Nat.succ_pos D⟩
    refine ⟨?_,fun u x=> ?_,fun u s x=>?_⟩
    · change ladd C μ k K β 0 (L K β d0) (ladder C 0 ((S).unit 0))=_; rw [ladder_unit]; exact pure_start H (he d0) (Nat.le_of_lt hk) _ _ (hp.charts K β hk d0).1
    · change ladd C μ k K β _ _ (ladder C _ ((Cells.standard C).conj h _ _))= star _; rw [ladder_conj]; exact purer H (he u) (Nat.le_of_lt hk) _ _ (hp.charts K β hk u).1 _
    change ladd C μ k K β _ _ (ladder C _ ((Cells.standard C).mirror h _ _ _))=_; rw [ladder_spin];exact rider H (he u) (Nat.le_of_lt hk) _ _ (hp.charts K β hk u).1 (hp.charts K β hk u).2 s _
end YM.MergeProof.East
