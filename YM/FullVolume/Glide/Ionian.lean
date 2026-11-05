import YM.FullVolume.Roll.Meridian
import YM.FullVolume.Glide.Triumph
import YM.FullVolume.Amp.Gavel
/- field convergence in common normalized topology.Bi.Coupon no mixed teams. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
open Pass FullVolume.Urns FullVolume.Ray Contest FullVolume.Amp Lark.Glide Push.AbsoluteSums
open UniformSpace
variable {R:Run G} (T:Campaign R) (n N:ℕ)
local notation "I"=> Fin (N+1)
local notation "Θ"=> T.gains
local notation "Ω"=> R.alloy.B.a.clock.hatBeta
local notation "Y" => R.alloy.B.a
local notation "O"=> halls T n N
lemma fillspace {c:Side}(X:Urns.Price G c)(K:Team X): ∃ f:World K→L[ℝ] Completion (Show X), (∀ x,‖f x‖ ≤ ‖x‖)∧ ∀ x:Home K,f (World.ready (x:Completion (Home K)))= ↑(x.val:Show X):=by
    let e: Home K →L[ℝ] Completion (Show X):= (Completion.toComplL (𝕜:=ℝ) (E:=Show X)).comp (Home K).subtypeL
    let T:= Completion.toComplL (𝕜:=ℝ) (E:=Home K); have hv:Isometry T:= Completion.coe_isometry; have he: DenseRange T:= Completion.denseRange_coe; let S:=e.extend T; let P:World K →L[ℝ] Completion (Show X):= show Completion (Home K) →L[ℝ] Completion (Show X) from S
    refine ⟨P,fun x=>?_,fun x=>e.extend_eq he hv.isUniformInducing x⟩; let y: Completion (Home K):=x; change ‖S y‖ ≤ ‖y‖; apply isClosed_property he (isClosed_le S.continuous.norm continuous_norm) _ y; intro q; unfold S; rw [e.extend_eq he hv.isUniformInducing q]; exact ((Completion.norm_coe q.val).trans (Completion.norm_coe q).symm).le
private lemma twirl {X Ix:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Ix][NormedSpace ℝ Ix][CompleteSpace X][CompleteSpace Ix](f:X→L[ℝ] Ix)(he:∀ x,‖f x‖ ≤ ‖x‖)(P:Beam X):∃ B:Beam Ix, ‖B‖ ≤ ‖P‖∧∀ s:sun,Beam.read Ix s B=f (Beam.read X s P):=by
    let g(i:ℕ):= f (P i); have hx: SumBudget (fun i=> ‖g i‖) ‖P‖:= budget_mono (togg P) (fun i=>norm_nonneg _) fun i=> he (P i)
    let T:Beam Ix:= ⟨g,memℓp_gen (by simpa only [ENNReal.toReal_one,Real.rpow_one] using hx.2.1)⟩
    refine ⟨T,(paid T|>.tsum_eq.symm).trans_le hx.2.2,fun s=>?_⟩; have hv:= (f.hasSum (Beam.spar P (abs_le.mpr s.property|>.trans (le_refl _)))) -- simplify
    change ∑' i,s.val^i • g i=f _; simp_rw [map_smul] at hv; exact hv.tsum_eq
-- contours.s
lemma specter (i:Fin (N+1)):∃ P:Beam ℝ,∃ X:Beam (cloud Y i n), ‖P‖ ≤16*Ω i∧ ‖X‖ ≤1∧∀ s:sun, ∀ p:Contest N n T.L, bonusB p=ask Y s → p.beta i=Beam.read ℝ s P ∧ Window.coats T.gains (halls T n N) p i=Beam.read _ s X :=by
    obtain ⟨V,B,h,h',H⟩:= T.coupons n N; obtain ⟨f,hf,hK⟩:=fillspace (stageP Y i.val n) (O|>.plan i (headB i))
    let P:Beam (World (O|>.plan i (headB i))):= V i; obtain ⟨X,hX,hU⟩:= twirl f hf P
    refine ⟨B i,X,h' i,hX.trans (h i),fun s p hp=>?_⟩; obtain ⟨h,hb⟩:= H s p hp i
    refine ⟨h,?_⟩; rw [hU s]; change Window.coats _ _ _ _= f (Beam.read (rom O i) s (V i)); rw [← hb]; unfold Window.coats Window.gifts; rw [dif_pos (headB i)]; exact (hK (p.chair Θ O i)).symm
lemma topfit (m V:ℕ):∃ (P:Beam ℝ)(X:Beam (cloud Y m n)), ‖P‖≤16*Ω m∧ ‖X‖≤1∧ ∀ h:m≤V,∀ s:sun,∀ p: Contest V n T.L, bonusB p=ask Y s→p.beta ⟨m,by omega⟩=Beam.read ℝ s P ∧ Window.coats Θ (halls T n V) p m= Beam.read _ s X :=by
    by_cases he:m≤ V
    · obtain ⟨P,X,h,H,hP⟩:= specter T n V ⟨m,by omega⟩; exact ⟨P,X,h,H,fun _=> hP⟩
    exact ⟨0,0,(norm_zero).trans_le (mul_nonneg (by norm_num) (T.gains.largeG.scale _|>.floor|>.le)), by simp,fun h=> False.elim (he h)⟩
variable (hR:Locrian R)(hp:Jams.Wild R.kit.shape R.alloy.delay)
include hp hR
lemma sprang (m:ℕ): ∃ (f:ℕ→Beam ℝ)(F:ℕ→ Beam (cloud Y m n)) (P:Beam ℝ)(X:Beam (cloud Y m n)), ‖P‖≤16*Ω m ∧ ‖X‖ ≤1 ∧ (∀ k,Tendsto (fun i=>f i k) atTop (𝓝 (P k))) ∧ (∀ k,Tendsto (fun i=> F i k) atTop (𝓝 (X k))) ∧ ∀ i,‖f i‖≤16*Ω m ∧ ‖F i‖≤1∧∀ h : m ≤ i, ∀ s:sun, ∀ p:Contest i n T.L, bonusB p=ask Y s → p.beta ⟨m,by omega⟩=Beam.read ℝ s (f i) ∧ Window.coats Θ (halls T n i) p m=Beam.read _ s (F i):=by
    choose f F h h' H using topfit T n m
    have ht (s:sun): (∃ p,Tendsto (fun i=> Beam.read ℝ s (f i)) atTop (𝓝 p))∧∃ p,Tendsto (fun i=>Beam.read _ s (F i)) atTop (𝓝 p):=by
        choose p hp using fun N:ℕ => Contest.born (N:=N) (n:=n) T.gains (Contest.onLine T.gains s)
        obtain ⟨f',X',g,hK⟩:=Lark.Glide.Window.allB T.gains hR.1 hR.2 ‹Jams.Wild R.kit.shape R.alloy.delay› tendsto_id p (fun i=>halls T n i) (tendsto_const_nhds (x:= ask (R.alloy.B.a) s)|>.congr' (Eventually.of_forall fun n=>(hp n).symm))
        exact ⟨⟨_,(Window.palm tendsto_id hK m).congr' ((eventually_ge_atTop m).mono fun x hx=> H _ hx _ _ (hp x)|>.1)⟩,_,(hK.fields m).congr' ((eventually_ge_atTop m).mono fun x hx=>H _ hx _ _ (hp x)|>.2)⟩
    obtain ⟨P,hp,hZ⟩:=Beam.issueR h (fun s=>ht s|>.1); obtain ⟨X,hX,hF⟩:=Beam.issueR h' (fun s=> (ht s).2); exact ⟨f,F,P,X,hp,hX,hZ,hF,fun i=>⟨h i,h' i,H i⟩⟩
end YM.PhysicalNext.Repeat.Legato.Campaign
