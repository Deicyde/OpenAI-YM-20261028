import YM.UVExtension.Whirl.Tips
import YM.UVExtension.Guild.Fair
import YM.UVExtension.Concert.Pure
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Guild
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ} (hm:m<N) {ε:ℝ}


open Whirl
variable (hG:G.Simple) (T:Crest R ε) {P P₁ P₂:(RG.Rep G (A.B.a.S.side (m+1) n))} (H:Guide A.B R.shape N m n P) (W: Zeal R.target R.shape A N m) (k:ℕ)(Tk: Wheeled R H W (ε:=ε) k)(hr:P.p=(A.B.a.budget (m+1)))

-- token points independent with beta stage. k is fixed by base. reach conditions in Chronicle/Launch.
structure Item (P₁: (RG.Rep G (A.B.a.S.side (m+1) n))) where
    atH: Guide A.B R.shape N m n P₁
    price : Opera.Price A.B R.shape N m n P₁ atH
    related : KinBase P P₁
    aisle : P₁.beta∈ band A.B.a (m+1)

variable (F:Item R (P:=P) (N:=N) P₁) (J:Item R (P:=P) (N:=N) P₂)

namespace Item
abbrev links: Match.Alliance H F.atH 1 0:= parallel F.related
def song := Chosen R H W k F.atH (F.links R H) F.aisle
def coupon := Averaging.delta ((Guild.Market R H).read (F.song R H W k))
-- candidate scalar independent of forest
-- Delta as reassembled. full step can be considered even out of band below, transfer requires in above.
abbrev first := P₁.beta + A.B.kin.alpha N m+ F.coupon R H W k

def issue:= finish (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) (shelves (Guild.Market R H) (A.B.kin.path N m) (A.B.a.budget m)) (branch (Guild.Market R H) (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) (F.song R H W k) (A.B.kin.alpha N m)) (F.first R H W k) (flatRate A.B.a m n P₁)

lemma same (F':Item R (P:=P) (N:=N) P₁): F.song R H W k = F'.song R H W k:=
    sameArts (A.B.a.budget m) k (A.B.kin.alpha N m) (show KinBase P P from ⟨rfl,rfl,rfl,rfl,rfl⟩) _ _ rfl rfl (Rain.screens R.target A m) _ (show Cousin P₁ P₁ from ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩)
include hG hm hr T Tk
lemma honor : (F.issue R H W k).activities.Valid (A.B.a.budget m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m):=
    ((Guild.standing R hm H W k F.atH (F.links R H) rfl F.related F.price F.aisle (F.related.point.symm.trans hr) T Tk hG).2).1

variable {s:Signed}{b: Site (A.B.a.S.side m n)}
variable (X₁:P₁.activities.Moves s ((A.B.a.clock.op m n).ratio.embed b)) (X₂:P₂.activities.Moves s ((A.B.a.clock.op m n).ratio.embed b))
private def perT: ((Market R H).read (F.song R H W k)).Moves s b:=
    let h:= Whirl.gales (Beam.marquee H (A.B.a.budget m)) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) (Guild.Tips R H k F.atH (F.links R H)) (GleamV R W k F.aisle) (SightV R H W k F.atH (F.links R H) F.aisle) s b (Whirl.tips H (A.B.a.budget m) Chi.canonical _ s b X₁ k (A.B.kin.alpha N m))
    Whirl.pellet (hak _) (A.B.a.budget m) h

private def perP : Whirl.Takes s b (shelves (Market R H) (A.B.kin.path N m) (A.B.a.budget m)) (branch (Market R H) (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) (F.song R H W k) (A.B.kin.alpha N m)):=
    let hv:= ready R hm H W k F.atH (F.links R H) rfl F.related F.price F.aisle (F.related.point.symm.trans hr) T Tk
    Whirl.ember hG hv (Return.enough_room A.B m n) (A.B.kin.alpha N m) (F.coupon R H W k) s b (perT R H W k F X₁)

def perFinal: (F.issue R H W k).activities.Moves s b :=
    Whirl.pellet (folio G (A.B.a.S.side m n)) (A.B.a.budget m) (widened (perP R hm hG T H W k Tk hr F X₁))
omit hm hG T Tk hr in
private lemma perTogether (hh: Twins X₁ X₂): Twins (perT R H W k F X₁) (perT R H W k J X₂):= by
  let q:= Beam.marquee H (A.B.a.budget m)
  let Y: KinBase P₁ P₂:= ⟨F.related.reg.symm.trans J.related.reg,F.related.forced.symm.trans J.related.forced,F.related.point.symm.trans J.related.point,F.related.path.symm.trans J.related.path,F.related.clip.symm.trans J.related.clip⟩
  let h:= tips_twin H (A.B.a.budget m) Chi.canonical (F.links R H) (J.links R H) X₁ X₂ Y hh rfl k (A.B.kin.alpha N m) (A.B.kin.alpha N m)
  exact Whirl.fuseTwins _ _ _ _ (Whirl.rotation q _ _ _ _ _ s b _ _ _ _ _ h)
lemma perfect (he:Twins X₁ X₂) : Twins (perFinal R hm hG T H W k Tk hr F X₁) (perFinal R hm hG T H W k Tk hr J X₂):= by
  apply Whirl.fuseTwins _ _ _ _ (wideTwins _ _ _)
  exact Whirl.moves hG (ready R hm H W k F.atH (F.links R H) rfl F.related F.price F.aisle (F.related.point.symm.trans hr) T Tk) (Return.enough_room A.B m n) _ _ (ready R hm H W k J.atH (J.links R H) rfl J.related J.price J.aisle (J.related.point.symm.trans hr) T Tk) _ _ (perTogether R H W k F J X₁ X₂ he)
end Item
end YM.UVExtension.Guild
