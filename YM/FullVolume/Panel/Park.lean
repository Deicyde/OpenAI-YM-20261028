import YM.FullVolume.Panel.Beam
import YM.FullVolume.Umbra.Liner

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
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
set_option quotPrecheck false
local notation "G'"=> Labels.frames G
open Matric
open Guard
namespace Boutique
variable {meshT:ℕ→∀ p,RG.Shoot.Trail A.B.a p}{N p m d:ℕ}
local notation "H!"=> A.B.bake.make meshT
local notation "μ"=> (0:ℝ)
variable (U: Boutique X meshT N p m)(choice: (A.B.bake.make meshT).Selected)(hd:d+3 ≤ A.B.a.clock.J m)
local notation "ris"=> (H!).rep N p (m+1)
local notation "R'"=> (H!).rep N p m
local notation "fa"=> (Labels.frames G).level d
local notation "J"=> A.B.a.clock.J (m+1)
local notation "t"=> A.B.a.clock.J m
open PhysicalNext.Repeat.Rain Pressure ConnectedActivityE6 Blaze Blaze.March Lim Umbra
open Ovens Match
local notation "D"=> U.stock.ordinal
local notation "Q"=> A.B.a.budget m
local notation "B"=> A.B.kin.path N m
local notation "x"=> A.B.a.clock.hatBeta m
local notation "c"=> (A.B.a.params m).clip
local notation "E"=> Trio.base (Rain.lint X.target A m) (radiusB x)
local notation "s"=> U.stock
local notation "L"=> A.B.a.clock.op m p
abbrev sale := houseS U.stock center
abbrev ask := noteX U.stock.H U.stock.knows (0:ℝ)
local notation "γ"=> A.B.kin.alpha N m
abbrev rent := U.stock.W.offers U.stock.ordinal (noteX U.stock.H U.stock.knows 0)
local notation "f"=> U.stock
local notation "V"=> U.sale
lemma onceB : (s).H.sister center= staple («H»:=V) («J»:=V) rfl rfl rfl:=by
   have h:(s).H.base=V:=rfl
   let T: Alliance (s).H.base V 1 0:= staple rfl rfl rfl
   have hk {Y Z:Alliance (s).H.base V 1 0}(h:Y.units=Z.units): Y=Z:= by cases Y; cases Z; congr
   exact hk ((s).H.agrees _)
lemma fresh (q:Lotus.Leaf ris): pupil U.stock center q = Umbra.prismK V Q γ D (Rain.screens X.target A m) E U.rent B c q:=by
    let F:=graft ((s).H) (s).knows (s).W D (0:ℝ)
    have hx : (s).H.latch 0=center:=(s).H.click _ center.property
    have hz:(s).X'= Marlin.pluck Q (Umbra.bubble V Q E):=rfl
    have hD:(s).H.sister center=(staple («H»:=V) («J»:=V) rfl rfl rfl):= onceB U
    have hF: F= Umbra.oval V Q γ D (Rain.screens X.target A m) E U.rent:=by
       unfold F graft uptick beacons lights; rw [hx,hD];rfl
    have he : (s).V' (0:ℝ)=Marlin.poursP Q (Umbra.bubble V Q E) F:=rfl
    unfold pupil
    change final.frigid (shelves (s).X' B Q) (branch (s).X' B c Q ((s).V' 0) γ) _ Q=_
    rw [he,hz,hF]; unfold Mallow.shifting; dsimp only -- change per t
    rw [hD]; -- also graft at center.val
    simp_rw [show graft (s).H (s).knows (s).W D (center:ℝ)=_ from hF];rfl
end Boutique
end Bandage
end YM.PhysicalNext.Repeat.Legato
