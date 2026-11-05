import YM.UVExtension.Rainfall.Ascot
import YM.UVExtension.Mast.Theme
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
include hm
lemma slots1 : HasSlots (c1).p (c1).activities:= Vintage.YM.PhysicalNext.Repeat.Graces.Nest.samples hG (housed S (fun _ _=> z)) N (m+1) n hm
lemma slots0 : HasSlots (((K0).result beam0).p) (((K0).result beam0).activities):=by rw [← ponds]; exact Vintage.YM.PhysicalNext.Repeat.Graces.Nest.samples hG (housed S (fun _ _=> z)) N m n hm.le
include R hd
omit hm in
lemma readC : Push.Local.Readable (hol G) π (c1).p ((T).S.side (m+1) n) (title G (M.p.profile (A.B.a.clock.J (m+1)))):=by
   have hx := step_paid A.B.a m
   let j:= A.B.a.clock.J (m+1); have hj:d ≤ j:= (by omega : d ≤ A.B.a.clock.J m).trans hx.1
   rw [show title G (M.p.profile j) = authors T (m+1) by unfold title authors; rw [params_eq A.B.valid] ]
   exact lively R.clock hj (n:=n)
local notation "Φ"=> Keeper.sufficient (slots0 S N m n z hm)
local notation "Υ"=> slots1 S N m n z hm
local notation "V"=> (readC S R d N m n z hd)
set_option maxHeartbeats 680000 in
lemma talent : ∃ L': Banner A.B.a (F) (hol G) n m, Waged K0 beam0 V Υ Φ L':= gala hm (housed S (fun _ _=>z)) R.r K0 beam0 (ponds S N n m z hm) rfl hG R.tunes R.furthering R.clock R.stamp _ _ _ hd
variable (he:(1+2*(A.B.a.params m).columns)*Doors.rate (A.B.a.S.block m) ≤ Bid.barunit (A.B.a.S.block m))
local notation "Υ1"=> slots1 S N m n (v N n) hm
local notation "Φ1"=> Keeper.sufficient (slots0 S N m n (v N n) hm)
local notation "V1"=> readC S R d N m n (v N n) hd
local notation "cF"=> C (A.B.a.clock.J (m+1))
include he
set_option maxHeartbeats 640000 in
lemma flock (h: Waged K1 beam0 V1 Υ1 Φ1 L') : Lacing.Tribe (p:=n) (A:= O!) («H»:=A.B.a) m L' (Doors.rate ((T).S.block m)) (cF) cF ∧ Pact π H N n (hol G) W (D! N n) sT m hm L' ∧ (∀ i:(F).Index,i≠0→ sparkT K1 beam0 (Circlet.lark (g0) i V1 Υ1) d):=by
    have hv:=(housed S v); let t:= (A.B.a.params (m+1)).columns; let i:=A.B.a.clock.J m; let j:=A.B.a.clock.J (m+1); have hx:= step_paid A.B.a m; have hh:d≤ i:= (le_trans (Nat.le_add_right d _) hd)
    have hC : Buys H F W m cF (Doors.rate ((T).S.block m)):= R.clock.fits H rfl m d hh
    have he' : (H).S.block m=P.L j:= Push.PriceCompiler.block_eq A.B.valid m
    have hu : sT m = 2*(Real.exp (g0).p.supportExponent* Cub.title G (M.p.profile j)):=by unfold waybill; rw [params_eq A.B.valid]; rfl
    obtain ⟨Q,hQ,T',ht,hT,hS⟩:= pomp hm R.songs R.PStage R.wait (Graces.feet hd R.clock) hv R.r K1 beam0 (ponds S N n m (v N n) hm) rfl hG R.tunes R.furthering R.corners R.shape R.clock R.stamp V1 Υ1 Φ1 h hd (zero_le_one.trans hC.cost)
    rw [show (T).S.block m = P.L j from he']
    rw [← hu] at ht
    refine ⟨⟨T',by rw [show (T).S.block m=P.L j from he']; exact hT,ht.map_norm⟩,⟨⟨_,Q,hQ,T',cF,_,Rainfall.seat π (Vintage.YM.Extra.Histories.Issue.trail (ministry S v)) N n m (hol G) g0 _ _ Q _ _ (ponds S N n m (v N n) hm) rfl L' _ he' ht HEq.rfl, by rw [he'.symm]; exact hC, by rw [he'.symm]; exact he⟩, ?_,(glyphBound (A.B.a) (m+1)).2⟩,hS⟩
    rw [hu]; exact mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (title_one ..)))
end YM.UVExtension.Mast
