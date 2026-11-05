import YM.UVExtension.Forest.Fluent
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
local notation "π"=> localSection G d
local notation "O!"=> hol G
variable {B:Org.Bolt A}(a:Upland.Arc Q S B)(t:ℕ→ℕ)
local notation "Φ"=> S.realBeat
structure Lisle (t:ℕ→ℕ)(A:Levels G) :Prop where
   tops i:i+3 ≤ A.clock.J (t i)
   gram d m : t d ≤ m → (1+2*(A.params m).columns)*Doors.rate (A.S.block m) ≤ Bid.barunit (A.S.block m)
variable (h: Lisle t A.B.a)
def cellar : Cellar S t R where
   line d n m i z:= tide S R d i m n z
   toll _ _ m:= Doors.rate (A.B.a.S.block m)
   vane _ _ m:= C (A.B.a.clock.J (m+1))
   lidS _ _ m:= C (A.B.a.clock.J (m+1))
   column _ _ i:= (A.B.a.params i).columns
   posts:= h.tops
   pay v d n i hi:= sails S v R d i n ((h.tops d).trans (A.B.a.fits.mono hi)) (h.gram _ _ hi)
   flow d n v b hv i hi:= curbstone S v R d i n a b hv ((h.tops d).trans (A.B.a.fits.mono hi)) (h.gram _ _ hi)

open MergeProof.Accent
-- lisle follows paper.Port.
lemma paidLinen {dN:ℕ→ℕ}{E:ℕ→ℕ→ℝ}{T:∀ d:ℕ,SectionData ((Labels.frames G).level d)}(hf:dN≤M.p.floorL)(h0:∀ i,i+3≤A.B.a.clock.J (t i))(hm:Legato.paper M.p E T dN) : Lisle t A.B.a:=by
    refine ⟨h0,fun i n hi=>?_⟩; let j:= A.B.a.clock.J (n+1); let v:= A.B.a.clock.J n; let L:=P.L j
    have hL: A.B.a.S.block n=L:=Push.PriceCompiler.block_eq A.B.valid n; have hx:= (h0 i).trans (A.B.a.fits.mono hi); have ht:v≤j:=A.B.a.fits.mono (Nat.le_succ _); rw [params_eq A.B.valid n,hL]; exact (hm _ _ (show i≤ j from by dsimp [v] at ht; omega) L ((hf j).trans (P.large j).need)).2.2.2 v ht
end YM.UVExtension.Mast
#print axioms YM.UVExtension.Mast.cellar
