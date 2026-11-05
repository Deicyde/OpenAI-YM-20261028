import YM.FullVolume.Gables.Major
import YM.FullVolume.Glide.Vac
/-! Palette convergence assumptions only | gathered stocks helper, inst. from Winter. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) {Y:Bolt A}
open YM.MergeProof
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Matric Guard
open RG.Shoot Lark Rain Blush Motion FullVolume.Shadow
variable {m N p k r d:ℕ}
open Boutique
set_option quotPrecheck false
local notation "a"=> A.B.a
open Boutique Pass FullVolume.Urns
variable {q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p}{f:ℕ→ℕ}
local notation "s"=> A.B.a.S
abbrev Log (q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p) (f:ℕ→ℕ) (p m:ℕ)(n:ℕ):= ((q n) (f n) p) m
structure Helmet (A:Alloy M P) (p:ℕ)(f:ℕ→ℕ) (q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p)(k:ℕ): Prop where
   cfront : Stationary.Artes.Cadre A.post A.B.kin
   rises : Next.Free.Amplify A.B.M
   sails : Tendsto f atTop atTop
   costa i (h:k ≤ i): CauchySeq (fun n=> (((q n) (f n) p) i).beta)
   earns i (h:k ≤ i): ∃ V:ℕ→ Show (stageP A.B.a i p), CauchySeq V ∧ ∀ n:ℕ,i ≤ f n → (((q n) (f n) p) i).activities= (V n).proper
lemma piano_truly {T:Type}[SeminormedAddCommGroup T]{F:ℕ→T}(h:CauchySeq F){u v:ℕ→ℕ}(he:Tendsto u atTop atTop)(hg:Tendsto v atTop atTop): Tendsto (fun n=> F (u n)-F (v n)) atTop (𝓝 0):=by
    refine Metric.tendsto_nhds.mpr fun ε hp=>?_
    obtain ⟨k,hk⟩:= Metric.cauchySeq_iff.mp h ε hp
    filter_upwards [he.eventually (eventually_ge_atTop k),hg.eventually (eventually_ge_atTop k)] with n hn hb; simpa [dist_eq_norm] using hk _ hn _ hb
namespace Helmet
variable (H:Helmet A p f q k)
variable (Q:∀ n,Branch X (q n) (f n) p k)
include H
-- echo for Heater across subscript. f common.One side atlas.
lemma atlas (m:ℕ)(h:k ≤ m){u v:ℕ→ℕ}(hu:Tendsto u atTop atTop)(hv:Tendsto v atTop atTop)(he:∀ i:ℕ,m<f (u i))(ht:∀ i:ℕ,m<f (v i)): Echo (q:=q ∘ u) (q':=q ∘ v) (f:=f∘u) (g:=f∘v) (m:=m) (fun i=>(Q (u i)).steps m h (he i)) (fun i=>(Q (v i)).steps m h (ht i)):= by
    obtain ⟨g,hx⟩:= cauchySeq_tendsto_of_complete (H.costa (m+1) (h.trans m.le_succ)); obtain ⟨V,hZ,h⟩:= H.earns (m+1) (h.trans m.le_succ); obtain ⟨W,Hf,hp⟩:= H.earns m (by assumption); let V':=V∘u; let W':= V∘ v
    have hx':= Pith.exportY hZ hu; have hz:=Pith.exportY hZ hv; have hh:=piano_truly hZ hu hv
    let L(i n:ℕ):= (((q n) (f n) p) i).activities; let Y n:= Log (A:=A) q f p m n
    have hf(i): L (m+1) (u i)=(V (u i)).proper:= h _ (he i); have hs i: L (m+1) (v i)=(V (v i)).proper:= h _ (ht i)
    refine ⟨⟨g,hx.comp hu,hx.comp hv⟩,?_,?_,?_⟩
    · change Angel (fun n=> (L (m+1) (u n)).regularOccurrence (A.B.a.budget (m+1))) (fun n=>(L (m+1) (v n)).regularOccurrence _); simp_rw [hf,hs]; exact Trill.gloves hx' hz hh
    · change Angel (fun n=> (L (m+1) (u n)).K) (fun n=> (L (m+1) (v n)).K); simp_rw [hf,hs]; exact Trill.hockey hx' hz hh
    have hy n: L m (u n)=(W (u n)).proper:= hp _ (he n).le; have hy' n:L m (v n)=(W (v n)).proper:= hp _ (ht n).le
    change Angel (fun n=> (L m (u n)).K) (fun n=> (L m (v n)).K); simp_rw [hy,hy']; exact Trill.hockey (Pith.exportY Hf hu) (Pith.exportY Hf hv) (piano_truly Hf hu hv)
end Helmet
-- Boot center from T.Winter, later gate T.P coupled.UTF.
section
open Muse Contest Campaign Lark.Glide UniformSpace
variable {R:Run G}(T:Campaign R) (hc:T.Winter)
local notation "A'"=> R.alloy.B.a
include hc
lemma helmed (p:ℕ):Helmet R.alloy p id (fun n=> R.T.history) 0:=by
    have hp := hc; let U N:=T.center N p; let y:= (A').clock.bar
    have he : (fun N=> (U N).bonusB)=(fun _=>y):= funext (fun n=> R.T.choice.reaches ..)
    have hf := hc.convergence p U y (by rw [he]; exact tendsto_const_nhds)
    refine ⟨hp.volumes.1,hp.volumes.2,tendsto_id,fun i _=>?_ ,fun i hi=>?_⟩
    · obtain ⟨u,v,hf,hs⟩:= hf i; exact hf.cauchySeq
    obtain ⟨u,v,hf,hs⟩:= hf i
    let f' (n:ℕ) (h:i ≤ n) := Contest.homeP T.gains (Campaign.halls T p n) (U n) i h
    let y(n:ℕ):Show (stageP (A') i p):= if h:i ≤ n then (f' n h).val else 0
    have hv (n:ℕ)(h:i ≤ n): ((R.T.history n p) i).activities=(y n).proper:=by unfold y; rw [dif_pos h]; exact (Contest.home_observe T.gains (Campaign.halls T p n) (U n) i h).symm
    have hw(n):Lark.Glide.Window.coats T.gains (Campaign.halls T p n) (U n) i=↑(y n):=by
       unfold Window.coats Window.gifts y; split; rfl
       rename_i h; rw [Completion.coe_zero]
    simp_rw [hw] at hs
    exact ⟨y, Metric.cauchySeq_iff.mpr (Metric.cauchySeq_iff.mp hs.cauchySeq|> fun h i hi=>by simpa only [Completion.dist_eq] using h i hi), hv⟩
end
end Bandage
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.helmed
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Helmet.atlas
