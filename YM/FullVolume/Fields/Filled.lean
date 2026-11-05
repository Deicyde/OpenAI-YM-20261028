import YM.FullVolume.Fields.Seat
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open YM.MergeProof MergeProof.Matric Guard
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Sever
open Extraction Extraction.Lease MergeProof.Accent
open Bandage
variable {G:Gauge}
namespace Campaign
set_option quotPrecheck false
open Pillars Boutique
variable {R:Run G} {T:Campaign R} (H:T.Winter)(W : Pillars R T)
local notation "A"=> R.alloy
local notation "L"=> R.alloy.B.a
variable (he:Jams.Wild R.kit.shape R.alloy.delay)
local notation "D"=> R.T
local notation "F"=> R.family
local notation "C'"=> Campaign.center T
include W H
lemma sees (p n:ℕ) (v:Fin n → R.family.book.Token)(x:Points n)(hv:Eves.ancestor R.family.S x)(hx:x∈ NoHit R.family.S p n)(he:Jams.Wild R.kit.shape R.alloy.delay): CauchySeq fun i=> FullVolume.evaluate R.family Extraction.Sequence.full p v [] i x:=by
    let h:= T.gains.SimpleR; have hi:= R.again h|>.1.scrim
    let HH:Rising R.kit (fun _=>R.T.history) id p 0:=⟨fun i=> W.yields i p,fun n i _ he=> (H.alignment p n (T.center n p) i he).1, helmed T H p⟩
    let t:=R.t; let Y'(i d n p:ℕ):= R.stories d n p
    have hp(d:ℕ):Rising.Tenable R.b HH (Y':∀ n d N p,TransferData _ (Issue.trail D) N p) R.tuning.receipts d R.t :=⟨Nat.zero_le _,R.accepts _,fun n h=> W.ports d n p h,fun n he=> R.makes.calibrated d n p he⟩
    let f i:= (v i).1
    let g i:= (v i).2
    have hZ:= HH.cinema h R.b («D»:=fun i=>R.doors) (ψ:=R.t) (Y':∀ n d N p,TransferData _ (Issue.trail R.T) N p) he R.tuning.receipts (u:=far L) (π:= waybill L) (φ:=near L) (δ:=renal L) (ζ:=fly L) (p':=mutt L R.Q) (Eventually.of_forall fun i=> Eventually.of_forall fun j=> hi.costs.pond R.family j i p R.w (far L) (waybill L) (near L) (renal L) (fly L) (mutt L R.Q) R.doors) (fun d=> (eventually_ge_atTop (R.t d)).mono fun i hi'=> hi.grows d i hi') hi.back f g (fun i=> hp (f i)) x hx hv
    exact hZ
include he
lemma purchased : FullVolume.Purchased R.family Extraction.Sequence.full:=by
    let S:= (F).S; let C:=F; intro n p v x hx
    let F':= FullVolume.evaluate R.family Extraction.Sequence.full p v []; obtain ⟨g,hg⟩:= Extraction.growFrom (nohitOpen S p n) (FullVolume.circulating (genuine R T.gains.SimpleR) Extraction.Sequence.full p v []) _ (Eves.dense S n) (fun x h=> sees H W p n v x h.1 h.2 he)
    have hy:x∈ NoHit S p n := fun i j hij=> ⟨timeAxis,hx i j hij _⟩
    refine Tendsto.cauchySeq (x:=g x) (Metric.tendsto_nhds.mpr fun ε he=> ?_); filter_upwards [hg.uniform ({x}) (Set.singleton_subset_iff.mpr hy) isCompact_singleton ε he] with i hi; exact hi x (Set.mem_singleton x)
theorem realUV : PositionsUV R.family Extraction.Sequence.full:= FullVolume.positioned _ (FullVolume.genuine R T.gains.SimpleR) (purchased H W he)
end Campaign
-- progress.Witness.Dev horizon same.L
open Campaign
lemma withUV (h:G.Simple)(w:ℝ)(hw:0<w):∃ (R:Run G)(T:Campaign R), Nonempty (Pillars R T) ∧ T.Winter∧ PositionsUV R.family Extraction.Sequence.full∧ R.family.path.levels.clock.kernel.penalty=w∧ (∀ f:Extraction.Order,∃ (g:Extraction.Order)(S:Table R.family.book), Nonempty (Spec.Final R.family (f.refine g) S)) :=by
   obtain ⟨R,T,hT,hp,⟨W⟩,hw⟩:= vendee h _ hw; have hW:= offers T hT hp; exact ⟨R,T,⟨W⟩,hW,realUV hW W hp,hw,(R.again h).2⟩
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.withUV
