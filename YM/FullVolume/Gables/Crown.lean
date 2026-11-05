import YM.FullVolume.Gables.Major
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
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) {Y:Bolt A}
open YM.MergeProof
local notation "H"=> Issue.trail Y
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Matric Guard
open RG.Shoot Lark Rain Blush Motion
variable {N p k r d:ℕ} (hz:Nest X Y)
open Boutique
set_option quotPrecheck false
local notation "a"=> A.B.a
local notation "F"=> (Labels.frames G).level d
local notation "L"=> localSection G d
local notation "σ"=> A.B.a.S
variable {D:∀ m,Desk G (A.B.a.S.side m p)}(hc:∀ i,Feeling A i p (D i))(hR:k ≤ r)(ht:d+3≤A.B.a.clock.J r)
def ruby (d:ℕ)(A:Levels G)(m:ℕ):= Doors.rate (A.S.block m)*(A.params (m+1)).columns*Motion.orbitCost ((Labels.frames G).level d)
abbrev CircleK (D:∀ m,Desk G (A.B.a.S.side m p))(d:ℕ)(m:ℕ):=Matric.Club ((Labels.frames G).level d) (hol G) (D (m+1)) (D m) ((A.B.a.params m).columns) ((A.B.a.params (m+1)).columns) (ruby d A.B.a m)
lemma rubies (d:ℕ)(A:Levels G)(m:ℕ): 0 ≤ ruby d A m:=mul_nonneg (mul_nonneg (Doors.rate_pos _).le (zero_le_one.trans (A.params (m+1)).columns_ge)) (zero_le_one.trans (Motion.orbitCost_one_le _))
namespace Branch
variable {q:ℕ→∀ p,Shoot.Trail A.B.a p} (Q:Branch X q N p k)
include b hz hc
include hG hR ht Q
def five (m:ℕ)(hm:r ≤ m)(he:m<N): CircleK (A:=A) D d m := tested (Q.heart b hR ht m hm he) (fair hG b Y _ hz (Q.steps _ (hR.trans hm) he) Q.choice) (tickets hG b (Q.steps _ (hR.trans hm) he) Q.choice (ht.trans (A.B.a.fits.mono hm)) hz|>.swing) (Q.notices hc ((hR.trans hm).trans m.le_succ) he) (Q.notices hc (hR.trans hm) he.le) b.clock.room b.clock.bank
noncomputable def tuition (i:ℕ)(h:r ≤ i): CircleK (A:=A) D d i:= if he:i<N then Q.five hG b hz hc hR ht i h he else Matric.coast _ _ _ _ (zero_le_one.trans (A.B.a.params _).columns_ge) (A.B.a.params _).columns_ge (rubies ..)
section feed
variable (m:ℕ)(hr:r ≤ m)(hx:m<N)
local notation "U"=> Q.steps m (hR.trans hr) hx
local notation "T'"=> Q.tuition hG b hz hc hR ht m hr
local notation "R"=> Q.five hG b hz hc hR ht m hr hx
local notation "s"=> (A.B.a.params (m+1)).columns
include hx
lemma argues : T'= R:=dif_pos hx
lemma sights (P:Gram F (hol G) (D (m+1)) s) : (T').leanings P= income hG b Y (ht.trans (A.B.a.fits.mono hr)) hz (U) Q.choice (Q.notices hc ((hR.trans hr).trans m.le_succ) hx) P:=by rw [argues hG b hz hc hR ht Q m hr hx]; rfl -- param order
lemma better (P:Gram F (hol G) (D (m+1)) s) : (T').drift P=Boutique.spends hG b Y (ht.trans (A.B.a.fits.mono hr)) hz (U) Q.choice (Q.notices hc ((hR.trans hr).trans m.le_succ) hx) (Q.notices hc (hR.trans hr) hx.le) P:=by
    rw [argues hG b hz hc hR ht Q m hr hx]; exact LinearMap.ext (fun x=>Gram.signs (Q.heart b hR ht m hr hx) (fair hG b Y _ hz (Q.steps _ (hR.trans hr) hx) Q.choice) (Q.notices hc ((hR.trans hr).trans m.le_succ) hx) (Q.notices hc (hR.trans hr) hx.le) b.clock.room b.clock.bank P x)
end feed
omit hG hz in
lemma sungAt (m:ℕ)(hr:r ≤ m)(hx:m≤N){V : TransferData ((Labels.frames G).level d) (A.B.bake.make q) N p}{S:Extra.Histories.Music ((Labels.frames G).level d) (A.B.bake.make q) N p}(H_:Branch.Velvet b Q hc hR ht V (hr.trans hx) S): Heard L (A.B.bake.make q) N p (hol G) m (S.tone m):= H_.2.2.1.earned m hr hx
omit hG hz in
def reading (m:ℕ)(hr:r ≤ m)(hx:m≤N){V : TransferData ((Labels.frames G).level d) (A.B.bake.make q) N p}{S:Extra.Histories.Music ((Labels.frames G).level d) (A.B.bake.make q) N p}(H_:Branch.Velvet b Q hc hR ht V (hr.trans hx) S): Gram ((Labels.frames G).level d) (hol G) (D m) (A.B.a.params m).columns:= Matric.measure (Q.sungAt b hc hR ht m hr hx H_) (Keeper.sufficient (Q.slots m (hR.trans hr) hx)) (Q.notices hc (hR.trans hr) hx)
section channel
variable (m:ℕ)(hr:r ≤ m)(hx:m<N){V : TransferData ((Labels.frames G).level d) (A.B.bake.make q) N p}{S:Extra.Histories.Music ((Labels.frames G).level d) (A.B.bake.make q) N p}(H_:Branch.Velvet b Q hc hR ht V (hr.trans hx.le) S)
local notation "R₀"=> reading b hc hR ht Q m hr hx.le H_
local notation "R₁"=> reading b hc hR ht Q (m+1) (hr.trans m.le_succ) hx H_
local notation "L'"=> tuition hG b hz hc hR ht Q m hr
include m hr hx H_
set_option maxHeartbeats 440000 in
lemma veering : R₀=(L').flow R₁∧ ∀ v,(V.entries m v).x=(L').leanings R₁ (V.entries (m+1) v|>.x):=by
    rw [Q.argues hG b hz hc hR ht m hr hx]
    let U':= Q.steps m (hR.trans hr) hx
    let heq:= ht.trans (A.B.a.fits.mono hr)
    have hf:= fair hG b Y heq hz U' Q.choice
    have he:= (tickets hG b U' Q.choice heq hz).swing
    have hb:= Q.sungAt b hc hR ht m hr hx.le H_
    have hd:= Q.sungAt b hc hR ht (m+1) (hr.trans m.le_succ) hx H_
    have hQ:=(H_.2.2.2 m hr hx).2.2
    let hB:=Q.notices hc ((hR.trans hr).trans m.le_succ) hx; let hA:=Q.notices hc (hR.trans hr) hx.le
    constructor
    · exact misses («H»:=A.B.bake.make q) (N:=N) (p:=p) (Y:=hol G) (P:=S.tone (m+1)) (Q:=S.tone m) b.clock.room b.clock.bank (Q.heart b hR ht m hr hx) hf he hB hA hd hb hQ
    intro x
    let B':=(Q.five hG b hz hc hR ht m hr hx).leanings R₁
    have hp : (V.entries m x).x= (S.tone m).index x:=by rw [H_.2.1]; exact hb.currents x
    have ht': (V.entries (m+1) x).x=(S.tone (m+1)).index x:=by rw [H_.2.1]; exact hd.currents _
    rw [hp,ht']; exact lever («H»:=A.B.bake.make q) (N:=N) (p:=p) (Y:=hol G) (P:=S.tone (m+1)) (Q:=S.tone m) b.clock.room b.clock.bank (Q.heart b hR ht m hr hx) hf he hB hA hd hb hQ x
end channel
end Branch
end Bandage
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Branch.veering
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Branch.sights
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Branch.better
