import YM.FullVolume.Dusk.Leads
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
namespace Branch
variable {q q':ℕ→∀ p,Shoot.Trail A.B.a p} (P0 :Branch X q N p k)(Q: Branch X q' N p k)
local notation "H!"=> A.B.bake.make q
local notation "Y!"=> A.B.bake.make q'
structure Courant : Prop where
    direct:∀ m,k ≤ m → m ≤ N → q N p m=q' N p m
    source:∀ m,∀ hm:k ≤ m,∀ h:m<N,Stitch (P0.steps m hm h) (Q.steps m hm h)
section price
variable {D:∀ j,Desk G (A.B.a.S.side j p)}(hc:∀ j, Feeling A j p (D j))(h:k ≤ r)(ht:d+3 ≤ A.B.a.clock.J r)
variable (V: TransferData ((Labels.frames G).level d) (A.B.bake.make q) N p) (W:TransferData ((Labels.frames G).level d) (A.B.bake.make q') N p)
variable (hi: r ≤ N)(hp:Courant P0 Q)(hV:Piano b P0 hc h ht V hi)(hW:Piano b Q hc h ht W hi)
local notation "L"=>localSection G d
include b hc ht
include h hi hV hW hp
lemma crash (m:ℕ) (hm:r ≤ m)(hf:m≤ N): V.entries m=W.entries m:=by
    obtain ⟨G0,h0,hG,hv,hJ⟩:= hV; obtain ⟨G1,h1,hZ,hs,hK⟩:= hW
    have he i (hr:r ≤ i)(ht:i≤N): (H!).rep N p i=(Y!).rep N p i:= hp.direct i (h.trans hr) ht
    have hY (i:ℕ)(hh:r ≤ i)(ht':i≤ N): (G0.tone i).plays=(G1.tone i).plays:=by
       induction ht' using Nat.decreasingInduction with
       | self=> rw [h0,h1,upstreams,upstreams]; have hx (x y:Rep G (A.B.a.S.side N p)) (hx:x=y) (p : HasSlots x.p x.activities)(q:HasSlots y.p y.activities):toper F L x (Keeper.sufficient p) (Keeper.blank p) d=toper F L y (Keeper.sufficient q) (Keeper.blank q) d :=by cases hx;rfl
                exact hx _ _ (he _ hi le_rfl) _ _
       | of_succ i hk ih=>
           have ha:=ih (hh.trans i.le_succ); obtain ⟨-,hv',Hr⟩:= hJ i hh hk; obtain ⟨-,h0',H'⟩:= hK i hh hk
           have hx: (G0.tone (i+1)).index=(G1.tone (i+1)).index:=by
              ext v:1; rw [← (hv.earned (i+1) (hh.trans i.le_succ) hk).currents v,← (hs.earned (i+1) (hh.trans i.le_succ) hk).currents v,ha]
           let v:= G0.tone (i+1); let w:= G1.tone (i+1)
           let g:= P0.steps i (h.trans hh) hk; let x:= Q.steps i (h.trans hh) hk
           let u:= P0.heart b h ht i hh hk; let u':=Q.heart b h ht i hh hk
           have hδ:u.plate=u'.plate:= g.strum b P0.choice Q.choice _ x (hp.source ..) (hp.direct _ (h.trans (hh.trans i.le_succ)) hk) (hp.direct i (h.trans hh) hk.le) -- orientation
           let J:= (H!).rep N p i;let I:= (Y!).rep N p i
           let U:= (H!).rep N p (i+1); let U':= (Y!).rep N p (i+1)
           have heq:J=I:=he _ hh hk.le; have hpq:U=U':=he _ (hh.trans i.le_succ) hk
           -- congr character.Apply.C.
           let Y (j:ℕ):= Site (A.B.a.S.side j p)
           funext y
           rw [Hr (hv.earned _ (hh.trans i.le_succ) hk), H' (hs.earned _ (hh.trans i.le_succ) hk), Matric.venture, Matric.venture,hx,ha]
           rw [show (P0.heart b h ht i hh hk).plate=u'.plate from hδ]
           -- still equality of collectP using dependent proof params. canonical .whirl after equality
           let F0 (I: Rep G (A.B.a.S.side i p))(U:Rep G (A.B.a.S.side (i+1) p))(ht:∀ m:Motion,Nonempty (I.activities.Moves m.1 0))(hv: HasSlots U.p U.activities):=collectP (R:=I) («L»:=U) u'.plate (Keeper.sufficient hv) (fun m'=> (ht m').some) (fun j=> capture (w.plays (w.index.symm (Size.axis F j))) (Keeper.sufficient hv)) (w.index y)
           have hA: F0 J U (fun m'=> (P0.choice.represents N p i hk.le).good.labels.moves m'.1 0) g.up= F0 I U' (fun m'=> (Q.choice.represents N p i hk.le).good.labels.moves m'.1 0) x.up:=by congr 1
           exact hA
    rw [hG,hZ]; exact hY m hm hf
lemma devices (he: V.Based (hol G) (localSection G d) r)(hx: W.Based (hol G) (localSection G d) r): V.terminal=W.terminal:=by
    ext v:1; rw [← he.reads,← hx.reads,crash b P0 Q hc h ht V W hi hp hV hW r le_rfl hi]
end price
end Branch
end Bandage
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Branch.devices
