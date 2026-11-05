import YM.FullVolume.Dusk.Law
import YM.FullVolume.Dusk.Gates
import YM.FullVolume.Literal
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
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp
open Pillars Bandage Pass Muse Contest Ovens
variable {R:Run G} (T:Campaign R)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
local notation "o"=> R.alloy.B.a.clock.bar
open Spirit Branch
open Boutique
open Extraction Extraction.Lease
variable (W: Pillars R T)
-- Diagram frame physical labels.Select.Stream REAL and branch.
namespace Face
open Filter Set Function MeasureTheory Metric Extraction Extraction.Lease Difference YM.FullVolume.Dusk Next.Extract MergeProof Cells Next.Rank
open Market
variable (H':T.Winter) (hx:Jams.Wild R.kit.shape R.alloy.delay)
local notation "C₁"=> centerF T W
variable (P:Face T W)(p:ℕ)
local notation "β"=> R.alloy.B.a.clock.bar
local notation "S'"=> P.V T W
local notation "R₀"=> R.family
include H' hx
open FullVolume Push.RelayDifference
variable (h : Tendsto (fun i=> evalV T W P p i) atTop (𝓝 R.alloy.B.a.clock.bar))
variable (hq : ∀ q:ℕ,q≠p→∀ n:ℕ, Courant (((centerF T W).score.mat n q)) (P.score.mat n q))
include h hq
lemma pinnacle : FixedBounds (P.V T W):=by
    let A:= P.V T W; let hG:= T.gains.SimpleR; have hp:= P.owns.makes ..; obtain ⟨hC,hF,⟨V,Z,L,e,hV,hZ⟩,hS⟩:= ridgeT W P.score P.owns
    obtain ⟨M,H⟩:= R.again hG
    obtain ⟨g,K,hK⟩:= H Order.full
    refine FullVolume.funding _ hp (fun d x l=>?_)
    set F := FullVolume.hops (Bid.upper A (fun _=>x)) l
    have hj : ∀ᶠ i in FullVolume.mesh, ‖(fun _=>x) i‖ ≤ ‖x‖:=Eventually.of_forall fun i=> le_rfl
    have hh:Tucked F (d+l.length):= (Tucked.up hp hG _ (FullVolume.Coin.from_bound hp (C:=A) (p:=fun _=>x) hj)).hops (FullVolume.borrowed (C:=A) (W:=fun i=> Push.RelayDifference.jump (A.path.levels.budget i)) (hF.shifts Order.full)) l
    obtain ⟨w,hw,hQ⟩:= prepared_many (C:=A) hp M.tabs hC hG hF (hops_solid (F:=Bid.upper A (fun _=>x)) (Eventually.of_forall fun i x=> A.continuousO ..) l|>.mono fun i hi=> hi 0) ((FullVolume.Stencil.visits hp _).hops l) hh
    obtain ⟨X,Y,hY⟩:= M.detectors K (d+l.length); have ht:= candles T W H' hx P p h K _ X Y hq hY
    exact FullVolume.improved (deal T W P _ _ X Y) hp M.tabs hS ht V Z hV e hZ (Funded.primaries hp hS (C:=A) (fun _=>x) hj) (fun N p x=> A.continuousO ..) w hw _ hQ (FullVolume.flown (by norm_num))
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.pinnacle
