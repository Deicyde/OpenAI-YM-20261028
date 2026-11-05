import YM.FullVolume.Shroud.Clan
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Urns
open Pillars Bandage Pass Muse Contest Ovens
variable {R:Run G} {T:Campaign R} (W:Pillars R T)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
local notation "o"=> R.alloy.B.a.clock.bar
open Spirit Branch
-- census proof.N can vary trail selection all periods. Gathering
variable {F:ℕ→∀ p N,Contest N p T.L}(C:∀ i,Cantata T (F i)) (p:ℕ) (b:ℝ)(H:T.Winter) (hp:Tendsto (fun i:ℕ=> (F i p i).bonusB) atTop (𝓝 b))
open UniformSpace Glide
include C H hp
lemma mount : Helmet R.alloy p id (fun i=> (C i).q) 1:=by
    let V':=fun i=>F i p i; have hf:= H.convergence p V' b hp; have hh(i m) (hm:1 ≤ m)(h:m≤ i): (C i).q i p m= (V' i|>.trail m):= (C i).palm i p (by omega) _ hm h
    refine ⟨H.volumes.1,H.volumes.2,tendsto_id,fun m hm=>?_,fun m hm=>?_⟩
    · obtain ⟨β,v,hβ,hv⟩:= hf m; exact Tendsto.cauchySeq (x:=β) (hβ.congr' ((eventually_ge_atTop m).mono fun i hi=>congr_arg Rep.beta (hh i m hm hi).symm))
    obtain ⟨β,v,hβ,hv⟩:= hf m; let f' (n:ℕ)(h:m ≤ n):= Contest.homeP T.gains (Campaign.halls T p n) (V' n) m h; let y (n:ℕ):Show (stageP (L!) m p):= if h:m ≤ n then (f' n h).val else 0
    have hw(n):Lark.Glide.Window.coats T.gains (Campaign.halls T p n) (V' n) m=↑(y n):=by
       unfold Window.coats Window.gifts y; split; rfl; rw [Completion.coe_zero]
    simp_rw [hw] at hv
    refine ⟨y, Metric.cauchySeq_iff.mpr (Metric.cauchySeq_iff.mp hv.cauchySeq|> fun h i hi=>by simpa only [Completion.dist_eq] using h i hi),fun n hn=>?_⟩; unfold y; change m ≤ n at hn; rw [dif_pos hn]; exact (congr_arg Rep.activities (hh n m hm hn)).trans (home_observe T.gains (Campaign.halls T p n) (V' n) m hn).symm
noncomputable def recur : Rising R.kit (fun i=> (C i).q) id p 1 := ⟨fun i=> C i|>.mat i p,fun n i hi hv=> by change ((C n).q n p i).path=_; change i ≤ n at hv; rw [(C n).palm n p (by omega) i hi hv]; exact (H.alignment p n _ i hv).1,mount C p b H hp⟩
lemma seatsN (d) (S:∀ i, Album T W (C i)): Rising.Tenable R.b (recur C p b H hp) (fun i=> (S i).record) R.tuning.receipts d R.t:=⟨W.late d,R.accepts d,fun n h=>(S n).spent _ n p h, fun n h=>(S n).priced _ n p h⟩
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.seatsN
