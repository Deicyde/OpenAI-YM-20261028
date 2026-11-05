import YM.UVExtension.Forest.Cave
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "V!"=> Voice F H n
local notation "μ!"=> Music F H N n
local notation "sT"=> Legato.Bandage.waybill (A.B.a)
variable {t:ℕ→ℕ}{B:Org.Bolt A} (a:Upland.Arc Q S B)
def roseA : Keys S:= fun _ _=> rose0 S -- convention rise
local notation "V"=> roseA S
def centerB := Org.Bolt.mk B.program (S.realBeat 0) ((show B.history=S.realBeat 0 from a.atPeak) ▸ B.sticks) (a.centered) (a.atPeak ▸ B.moves)
local notation "B0"=> centerB S a
lemma projected : B=B0:=by
   rcases B with ⟨X,Y,U,g,h⟩; have hx:Y=S.realBeat 0:=a.atPeak; subst Y; rfl
lemma ridge : Graces.Nest Q B0 :=by exact ⟨fun N p=>S.slotReady N p (Uses.centerP _), fun N m p hm=> (S.housing N p (Uses.centerP _) m hm).2.symm⟩
variable (U : Cellar S t R)
local notation "C0"=> Cellar.yard V U
include a
lemma calibrated : (C0).Makes:=by
   have hp:= Cellar.intakeV (V) U; obtain ⟨w,h,k,q,n,v⟩:= hp; exact ⟨(B0).choice,h,k,q,n,v⟩
lemma charts (d N p) (hx:t d ≤ N) : Freight (B0) (ridge S a) N p d (Cellar.gate V U d N p) (t d) W (Orchard.roof S V N p):=by
    obtain ⟨A,B,C,D,E⟩:= U.freed V d N p hx; exact ⟨A,B,C,D,E⟩
lemma cliffs (m N n) (hm:m<N): Climbs Q B0 N m n (roof S V N n m hm):=by
    obtain ⟨l,v,Q,U,y,hD,hT,hS⟩:= routes S V N n m hm; exact ⟨l,v,Q,U,y,hD,hT,hS⟩
end YM.UVExtension.Mast
