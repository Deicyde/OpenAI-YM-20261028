import YM.FullVolume.Gables.Marble
import YM.FullVolume.Mark.Vega
import YM.FullVolume.Mark.Sages
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
variable {q:ℕ→∀ p,Shoot.Trail A.B.a p} {m N p k r:ℕ} (hz:Nest X Y)
open Boutique
set_option quotPrecheck false
local notation "a"=> A.B.a
local notation "H'"=> A.B.bake.make q
local notation "s"=> A.B.a.S
-- structure Stores independent `D : Display`
structure Branch (X:Factor A)(q:ℕ→∀ p,Shoot.Trail A.B.a p) (N p k':ℕ) where
   choice: (A.B.bake.make q).Selected
   slots : ∀ i:ℕ,k' ≤ i → i≤ N → HasSlots ((A.B.bake.make q).rep N p i).p ((A.B.bake.make q).rep N p i).activities
   steps : ∀ i:ℕ,k' ≤ i → i < N → Boutique X q N p i
variable (Q:Branch X q N p k)
variable {D:∀ m,Desk G (A.B.a.S.side m p)}(hc:∀ i,Feeling A i p (D i))
namespace Branch
include Q
include hc in
lemma notices (h:k ≤ m)(he:m≤N): Well ((H').rep N p m) (D m) (Real.sqrt (A.B.a.clock.forcedAllowance m)):=by
    have ht:= Q.choice.represents N p m he; exact (hc m).carts ht.vac (Q.slots m h he)
variable {d:ℕ} (hR:k ≤ r)(ht:d+3≤A.B.a.clock.J r)(V:TransferData ((Labels.frames G).level d) (A.B.bake.make q) N p)
variable (h:r ≤ N)
local notation "F"=> (Labels.frames G).level d
local notation "L"=> localSection G d
include b
-- no `position sample` dependence. tags `P at each d layer`
abbrev heart (j:ℕ)(hi:r ≤ j)(hi':j<N): Tool ((Labels.frames G).level d) (A.B.bake.make q) N p j := (Q.steps j (hR.trans hi) hi').castT b Q.choice (ht.trans (A.B.a.fits.mono hi))
include Q h hR ht hc
abbrev Velvet (Z: Extra.Histories.Music ((Labels.frames G).level d) (A.B.bake.make q) N p): Prop := Z.tone N = Guard.summit F L (H') N p (Keeper.sufficient (Q.slots N (hR.trans h) le_rfl)) (Keeper.blank (Q.slots N (hR.trans h) le_rfl)) d ∧ V.entries=(Z.draft (H')).inits∧
    Matric.Portal (localSection G d) (A.B.bake.make q) N p (hol G) K r (fun j hi he=>(Q.steps j (hR.trans hi) he).gate) (waybill A.B.a) (fun j hi hv=> Q.notices hc (hR.trans (hi.trans j.le_succ)) hv) (Q.heart b hR ht) Z
abbrev Piano : Prop:= ∃ Z: Extra.Histories.Music ((Labels.frames G).level d) (A.B.bake.make q) N p, Velvet b Q hc hR ht V h Z
include hG hz
set_option maxHeartbeats 420000 in
lemma composing : ∃ T:TransferData F (H') N p,T.Based (hol G) L r∧ Piano b Q hc hR ht T h:=by
    let W:= Q.slots N (hR.trans h) le_rfl; let V':=Guard.summit F L (H') N p (Keeper.sufficient W) (Keeper.blank W) d
    have he: d ≤ A.B.a.clock.J N:= (Nat.le_add_right d 3).trans (ht.trans (A.B.a.fits.mono h)); have hs:= sound G d
    have hv : OnTop L (H') N p (hol G) V' := summon F L (H') N p _ _ Q.choice d hs (Doors.cameras_ge G d) (fun i=> Doors.cameras_holds G d _ i 0) ((b.clock.sequences N d he).receipts p 0)
    have hX := MergeProof.voice L (H') N p (Keeper.sufficient W) (Keeper.blank W) d Q.choice hs hv
    have hp (m:ℕ)(hm:r ≤ m)(hf:m<N):∃ c v X R, Tool.Cap (Q.heart b hR ht m hm hf) L (hol G) K ((Q.steps m (hR.trans hm) hf).gate) R c v (waybill A.B.a m) X ∧ Afford ((Q.heart b hR ht m hm hf).plate) (hol G) ((H').rep N p (m+1)) ((H').rep N p m):=by
       let U:= Q.steps m (hR.trans hm) hf; let hx:= tickets hG b U Q.choice (ht.trans (A.B.a.fits.mono hm)) hz; obtain ⟨c,p,hP⟩:=hx.chamber; exact ⟨_,_,_,_,hP,hx.swing⟩
    obtain ⟨U,hu,hQ⟩:= composeT K r _ _ (fun i hi hv=>Q.notices hc (hR.trans (hi.trans i.le_succ)) hv) b.clock.room b.clock.bank V' hv hX h hp
    obtain ⟨T,hT,h⟩:= Work.G08.answer K (H') b.clock.room b.clock.bank N p d r _ (U.draft (H')) (localSection G d) _ (Sung.clocks L (H') N p (hol G) K _ _ hQ.1)
    exact ⟨T,h,U,hu,hT,hQ⟩
end Branch
end Bandage
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Branch.composing
