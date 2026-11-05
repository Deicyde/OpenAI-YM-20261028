import YM.FullVolume.Stage.Crests
import YM.FullVolume.Amp.Gold
/-!
# Full campaign, strong complex dependence of tuned *finite* E/K masses and β. **All** Contest N n.L. Boundary real b, not collision. mass in actual Show seminorm via its canon. No UV here.
 -/
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
open Pass FullVolume.Urns FullVolume.Ray Contest FullVolume.Amp
open UniformSpace
variable {R:Run G} (T:Campaign R) (n N:ℕ)
local notation "I"=> Fin (N+1)
local notation "Θ"=> T.gains
local notation "Ω"=> R.alloy.B.a.clock.hatBeta
noncomputable def halls : Ops T.L N n:=Classical.choice (opal T.gains)
lemma bonus_center:bonusB (center T N n)=R.alloy.B.a.clock.bar:= R.makes.wilson.reaches ..
section prizes
set_option quotPrecheck false
local notation "O"=>halls T n N -- check order n,N
-- maps real.Literal up to seminorm. width unit.A.Radius and budget all coords
lemma coupons : ∃ (V:∀ i:I,FullVolume.Amp.Beam (rom (halls T n N) i)) (B:I→ FullVolume.Amp.Beam ℝ), (∀ i,‖V i‖ ≤1) ∧ (∀ i, ‖B i‖ ≤ 16*Ω i) ∧ ∀ s:sun, ∀ p:Contest N n T.L, bonusB p=ask R.alloy.B.a s→ ∀ i, p.beta i= FullVolume.Amp.Beam.read ℝ s (B i) ∧ realm T.gains (halls T n N) p i=FullVolume.Amp.Beam.read _ s (V i):=by
   let p:= center T N n; let T':= T.gains
   obtain ⟨U,h,hU⟩:= Contest.score T.gains (O) p (bonus_center ..)
   let V(i:I):FullVolume.Amp.Beam (rom O i):= FullVolume.Amp.Beam.arm (realm Θ O p i)+U.2 i; let q(i:I):= normedWidth (Ω i); let W(i:I):= q i • (FullVolume.Amp.Beam.arm (p.pitch i)+U.1 i); let B(i:I):= Ω i • Rally.sprint (W i)
   have he i:0<q i:= widthP (T'.largeG.scale _|>.floor)
   refine ⟨V,B,fun i=>?_,fun i=>?_,fun s r hr i=>?_⟩
   · have hv: ‖realm Θ O p i‖ ≤1/8:= (Completion.norm_coe _).trans_le (p.sparkN Θ O i)
     exact (norm_add_le ..).trans ((add_le_add ((Amp.Beam.armN _).trans_le hv) (Amp.Rally.perN h i|>.2)).trans (by norm_num [Amp.lux]))
   · have hp : 0 < Ω i:= (T'.largeG.scale _|>.floor); have hz: ‖W i‖ ≤4:=by
        have hP:= Rally.perN h i; have hh : q i*‖p.pitch i‖≤ 23/20:=by
           have hp:0 ≤ p.pitch i := by
             have hz:0 ≤ q i*p.pitch i:= le_trans (by norm_num) (p.dueP Θ i|>.1); exact nonneg_of_mul_nonneg_right hz (he i)
           rw [Real.norm_of_nonneg hp]; exact (p.dueP Θ i).2
        unfold W; rw [norm_smul,Real.norm_of_nonneg (he i).le]; apply (mul_le_mul_of_nonneg_left (norm_add_le ..) (he i).le).trans; rw [Beam.armN, mul_add]; have hv:q i ≤ 1/128:= (spare Θ i ⟨p⟩).2
        have hu := mul_le_mul hv hP.1 (norm_nonneg _) (by norm_num); unfold lux at hu; linarith
     unfold B; rw [norm_smul,Real.norm_of_nonneg hp.le,mul_comm (16:ℝ)]
     exact mul_le_mul_of_nonneg_left ((Amp.Rally.sprintN ..).trans ((mul_le_mul hz hz (norm_nonneg _) (by norm_num)).trans (by norm_num))) hp.le
   obtain ⟨he,hx⟩:=hU s r hr i
   have hz : (fromLambda (Ω i) (r.pitch i))=r.beta i:= r.spoken Θ _ (headB i)
   rewrite [←hz]; unfold B V; rw [map_smul, map_add,Amp.Beam.armL, Rally.sprintL]; unfold W; rw [map_smul,map_add,Amp.Beam.armL,←he]; exact ⟨rfl,hx⟩
theorem finite_coupling_arc : let a:=R.alloy.B.a
    0< beamWidth a ∧ (∀ s:sun,∃ p:Contest N n T.L,bonusB p=ask a s) ∧
    (∀ y y':Contest N n T.L,bonusB y=bonusB y' → ∀ m:ℕ,m≤N→y.trail m=y'.trail m) ∧
    (∀ i:Fin (N+1),∃ (f:ℂ→ℂ)(k:ℂ→FullVolume.Amp.hullB (rom (halls T n N) i)),
        (∀ s:sun,∀ p: Contest N n T.L,bonusB p=ask a s → f (s:ℝ)=p.beta i∧ k (s:ℝ)= FullVolume.Amp.golden _ (p.realm T.gains (halls T n N) i)) ∧ ∀ z:ℂ, ‖z‖<1 → AnalyticAt ℂ f z ∧ AnalyticAt ℂ k z):=by
   intro a
   refine ⟨Contest.raise Θ,fun s=>born Θ (onLine Θ s),fun x y he m hm=>one Θ O y x he m hm,fun i=>?_⟩
   obtain ⟨V,B,h,h',H⟩:= T.coupons n N
   refine ⟨shine Complex.ofRealCLM (B i), shine (golden (rom O i)) (V i),fun s p hp=>?_ ,fun z hz=> ⟨Amp.hol _ _ _ hz,Amp.hol _ _ _ hz⟩⟩
   obtain ⟨h,hb⟩:= H s p hp i; rw [Amp.opening, Amp.opening,h,hb]; exact ⟨rfl,rfl⟩
end prizes
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.finite_coupling_arc
#print axioms YM.PhysicalNext.Repeat.Legato.brink
