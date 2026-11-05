import YM.FullVolume.Gables.Pillar
import YM.FullVolume.Dusk.Craft
import YM.FullVolume.Dusk.Grove
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
variable {G:Gauge}(hG:G.Simple)
open YM.MergeProof
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) {Y:Bolt A}
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Matric Guard
open RG.Shoot Lark Rain Blush Motion FullVolume.Shadow
variable {m N p k r d:ℕ}
open Boutique
set_option quotPrecheck false
local notation "F"=> (Labels.frames G).level d
local notation "H"=> Issue.trail Y
-- brand verdict, captures branching.C.History.Other β homotopy
variable {x:ℝ}{F₀: Lyrics X x x}
namespace Boutique
variable {q:ℕ→∀ p,Shoot.Trail A.B.a p}
variable {g:ℕ→∀ p,Shoot.Trail A.B.a p}
section mold
local notation "H₀"=>A.B.bake.make q
local notation "H'"=> A.B.bake.make g
-- proof-safe reassociation. doesn't use composite eq of Histories
section sp
variable {x y: Rep G (A.B.a.S.side (m+1) p)}(he:x=y)(S:Spring X N m p 0 0 (fun _=> x))
abbrev refit := (show Spring X N m p 0 0 (fun _=> y) from he ▸ S)
lemma refit_eq : HEq S (refit he S):=by cases he;rfl
end sp
def Stitch (B:Boutique X q N p m)(P:Boutique X g N p m):Prop:= HEq B.stock P.stock
-- transfer Builder.Expect can copy if q* equality & include all W proofs. result.After.
variable (B:Boutique X q N p m)(h:(A.B.bake.make q).Selected)(h':(A.B.bake.make g).Selected)
variable (hd:d+3 ≤ A.B.a.clock.J m) (Z:Boutique X g N p m)(hz:Stitch B Z)(hp:q N p (m+1)=g N p (m+1))(he:q N p m=g N p m)
-- plate congr with S explicit
include hp he
include hz in
lemma strum : (B.castT b h hd).plate=(Z.castT b h' hd).plate :=by
    have hx (v w:Rep G (A.B.a.S.side (m+1) p))(he:v=w)(x y:Rep G (A.B.a.S.side m p))(h:x=y)(U: Spring X N m p 0 0 fun _=> v)(V:Spring X N m p 0 0 fun _=> w)(hs:HEq U V)(hq hF hr hT ht hv): placeQ U center x hq hr ht = placeQ (d:=d) V center y hF hT hv :=by
       cases he; cases h; cases hs; rfl
    change shade B.stock center _ _ _= shade Z.stock center _ _ _; rw [placedQ B.stock center B.down,placedQ Z.stock center Z.down]; exact hx _ _ hp _ _ he _ _ hz _ _ _ _ _ _
include B in
lemma fashioned (hh :Flavor F₀ B) : ∃ P':Boutique X g N p m, Flavor F₀ P' ∧ Stitch B P':=by
    have ha (u v:Rep G (A.B.a.S.side (m+1) p)) (U:Spring X N m p 0 0 fun _=>u) (h:u=v): HEq U (refit h U) ∧ U.result 0=(refit h U).result 0 ∧ U.W=(refit h U).W ∧ U.ordinal=(refit h U).ordinal:=by cases h; exact ⟨HEq.rfl,rfl,rfl,rfl⟩
    let hY:= q N p (m+1); let s:=refit (show q N p (m+1)=g N p (m+1) from hp) (B.stock)
    obtain ⟨hU,hv,hW,hQ⟩:= ha _ _ B.stock hp
    let V':Boutique X g N p m:=⟨s,(he.symm.trans B.taught).trans hv, (show (H₀).rep N p (m+1)=(H').rep N p (m+1) from hp) ▸ B.up,(show (H₀).rep N p m=(H').rep N p m from he) ▸ B.down,B.hx,hQ ▸ B.pays⟩
    exact ⟨V',⟨hQ.symm.trans (hh.1.trans (congr_arg _ (congr_arg Rain.listIn hp))), hW.symm.trans hh.2⟩,hU⟩
end mold
end Boutique
end Bandage
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Boutique.strum
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Boutique.fashioned
