import YM.UVExtension.Rainfall.Price
import YM.UVExtension.Rainfall.Planet
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Roost.Factor A} (S: Uses X hG) (v:Keys S) {C:ℕ→ℝ} {W:Bid.Worth}(R:Legato.Bandage X C W)
    (d N m n:ℕ) (z:Rose S)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T"=> A.B.a
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "sT"=> Legato.Bandage.waybill (A.B.a)
local notation "L!"=> Lacing.Banner («H»:=T) (F) (p:=n) (A:=hol G) m
variable (L': Lacing.Banner A.B.a ((frames G).level d) (hol G) n m)
local notation "c0"=> S.realBeat z.val N n m
local notation "c1"=> S.realBeat z.val N n (m+1)
variable (hm:m<N)(hd:d+3≤ A.B.a.clock.J m)
local notation "K0"=> (ray S N n m z hm).body
local notation "g0"=> S.realBeat (v N n).val N n (m+1)
local notation "K1"=> (ray S N n m (v N n) hm).body
local notation "Φ"=> Keeper.sufficient (slots0 S N m n z hm)
local notation "Υ"=> slots1 S N m n z hm
local notation "V"=> (readC S R d N m n z hd)
local notation "Υ1"=> slots1 S N m n (v N n) hm
local notation "Φ1"=> Keeper.sufficient (slots0 S N m n (v N n) hm)
local notation "V1"=> readC S R d N m n (v N n) hd
local notation "cF"=> C (A.B.a.clock.J (m+1))
open scoped BigOperators

def tide : Banner A.B.a (F) (hol G) n m:= if h:m<N ∧ d+3≤ A.B.a.clock.J m then (talent S R d N m n z h.1 h.2).choose else ⟨0,fun _=>0,fun _=>0, (cart (Keeper.sufficient (slots1 S (m+1) m n z (Nat.lt_succ_self m))))⟩
lemma follows : Waged K0 beam0 V Υ Φ (tide S R d N m n z) := by unfold tide; rw [dif_pos (show m<N∧_ from ⟨hm,hd⟩)]; exact (talent S R _ _ _ _ _ hm hd).choose_spec
open Bid
variable (hw:(1+2*(A.B.a.params m).columns)*Doors.rate (A.B.a.S.block m) ≤ Bid.barunit (A.B.a.S.block m))
include hw
lemma ting : Lacing.Tribe (p:=n) (A:= O!) («H»:=A.B.a) m (tide S R d N m n (v N n)) (Doors.rate ((T).S.block m)) (cF) cF ∧ Pact π H N n (hol G) W (D! N n) sT m hm (tide S R d N m n (v N n)) ∧ (∀ i:(F).Index,i≠0→ sparkT K1 beam0 (Circlet.lark (g0) i V1 Υ1) d):= flock S v R d N m n (tide ..) hm hd hw (follows (hd:=hd) ..)
local notation "t"=> Doors.rate ((T).S.block m)
local notation "w"=> ((T).params m).columns
include R v hd
lemma sails: Ability S d n R m (fun i=> tide S R d i m n (v i n)) t cF cF w ((T).params (m+1)).columns v:=by
   have hx:=(R.clock.fits H rfl m d (by omega)); obtain ⟨he,hq⟩:=paintBudget hx R.clock.room R.clock.bank
   exact ⟨fun i hi=>(ting S v R d i m n hi hd hw).1,fun i hi=>(ting S v R d i m n hi hd hw).2.1, he,le_rfl,hq⟩
end YM.UVExtension.Mast
#print axioms YM.UVExtension.Mast.sails
