import YM.Further.DENSE_MIXED_KERNELS.Stroke
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.MergeProof.Ballet
import YM.PhysicalNext.ORDERED_AFFINE_2B.Till
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Hood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat 
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ)
open Extra.Histories
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance i)
local notation "c'"=> H.S.side i p
-- generic input invariance under score;y
structure Chorus (V:Voice F H p i):Prop where
   pages j z: floatUp z 0 (profile (H.rep N p i).activities (V.plays j).forced)=profile (H.rep N p i).activities (V.plays (Motion.patch F z j)).forced
-- no expo via direct, from below.Other OR.Size.
lemma lyric {n:Side}{R:Rep G n}{P Q:Coefficient F n}{o:Site n}{v w a b t:ℝ} (hp:R.Lawful v w a b t)(hq: ∀ U,R.eval U≠0) (hv:Dominated P.forced)(hy:Dominated Q.forced)(hμ: P.density o B R=Q.density o B R)(hs: profile R.activities P.forced=profile R.activities Q.forced): P.exponentialEntry o B R=Q.exponentialEntry o B R:=by
   funext U; have h:=congr_fun hμ U; apply mul_left_cancel₀ (show (R.eval U:ℂ)≠0 from Complex.ofReal_ne_zero.mpr (hq U)); unfold Coefficient.density at h; rw [dress_eq hp hv,dress_eq hp hy] at h; rw [chamber (funext (fun j : Box n=> congr_fun (congr_fun hs j) U)) U ((dress_abs hp hv).summable _) ((dress_abs hp hy).summable _)] at h; exact add_right_cancel h
lemma chanting (A:Hol G) (V:Voice F H p i)(h:B.Sound A)(hp: Heard B H N p A i V)(hz:Chorus H N p i V)(ht:H.Selected)(hm:i≤N)(hN:∀ U,(H.rep N p i).eval U≠0)(v:F.Coeff)(m:Motion): stepUp m 0 ((V.plays v).exponentialEntry 0 B (H.rep N p i))=(V.plays (Motion.patch F m v)).exponentialEntry 0 B (H.rep N p i):=by
   obtain ⟨a,b,hA,_⟩:= rem_tabs.mp (hp.earns v|>.2); have hx:= (ht.represents N p i hm).good; obtain ⟨π⟩:= hx.labels.moves m.1 0
   let P:= audition π (V.plays v); obtain ⟨hQ,hf,hR,hK⟩:= audition_receipt m π ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S i p)) h (hp.earns v|>.1) hA
   rw [← bow m (V.plays v) 0 h π, show affine m.1 (0:Site c') 0=0 by simp [affine]]
   exact lyric B hx hN (rem_dominated (hR.bound le_rfl)) (rem_dominated (hp.earns _|>.2)) (hK.trans (hp.travels v m)) ((foyer m _ π _).trans (hz.pages v m))
set_option maxRecDepth 4608 in
lemma rip (F:Labels.Frame G d)(v:F.Coeff): (∑ i:Tally F, ‖chips F v i‖) ≤ orbitCost F * F.coeffSize v:=by
   rw [Fintype.sum_prod_type]; simp_rw [norm_chips];let s:= orbitCost F * F.coeffSize v; let X:= Motion
   calc _ ≤ ∑ _ : Motion, share * s := Finset.sum_le_sum (fun i _=> by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (patch_cost F _ _) share_pos.le)
        _ = _:= by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; have ht:=Motion.card_pos; rw [← mul_assoc,show (Fintype.card Motion:ℝ)*share=1 from mul_inv_cancel₀ (Nat.cast_ne_zero.mpr ht.ne'),one_mul]
-- edit syntax
variable (F)
set_option maxRecDepth 4608 in
lemma fixing {E:Type*}[AddCommGroup E][Module ℂ E](f:F.Coeff →ₗ[ℂ] E)(v:F.Coeff):
    ∑ i:Tally F,chips F v i • f (Motion.patch F i.1 (Size.axis F i.2))= f v:= by
   change _= f v; simp_rw [← map_smul,← map_sum]; exact congr_arg f (repaint_same F (LinearMap.id) (fun _ _=>rfl) v)
section
-- typo congrArg f.E
variable {V:Voice F H p i}(hv : ℕ)
end
end YM.MergeProof
