import YM.UVExtension.Mast.Rig
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

open Eyelet

open Cellar Pans Extraction Accent Motion Cells Push
variable {t:ℕ→ℕ} {R S} {v}(U: Cellar S t R) (B:Orchard.Rose S) (he: Tendsto (fun i=>(v i n).val) atTop (𝓝 B.val)) -- v inference
local notation "C'"=>Cellar.yard v U
local notation "f'"=> (U.gate v d N n)
local notation "g'"=> U.cantors v d n
local notation "bt"=> (fun i=> (g').feeds S v d n)
local notation "D'"=> D!
local notation "k0"=> t d
-- Exact terminal reads.Id moves.
lemma peak (hN:t d ≤ N): (U.gate v d N n|>.terminal) =((U.cantors v d n).song N|>.tone (t d)).index:= by
   apply LinearEquiv.ext; intro x
   obtain ⟨he,hv⟩:= (launch v U d N n).choose_spec hN
   let P:= (g').song N; rw [show (Cellar.gate v U d N n).terminal x = _ from (he.reads x).symm,hv]; exact ((U.cantors v d n|>.lyr N hN).earned.earned (t d) le_rfl hN).currents x

section orchestra
-- Primer matches any fixed vector. Actual r-value unique? use Quired.
-- Param K and ζ on exact Φ history.F
variable (K:ℕ→ℕ) (h: Scrim (Cellar.yard v U) W (far A.B.a) (waybill A.B.a) (near A.B.a) (renal A.B.a) (Legato.Bandage.fly A.B.a) (mutt A.B.a K) (Orchard.roof S v))
    (hK: Stock.Tabs A.B.a)
    (J k:ℕ)(hw:Stock.Tabs.opens A.B.a 1 J m)(x: ((frames G).level d).Index)(w:ℝ)(hy:0<w)
    (hp:t d ≤ m)(hk:m≤ k)(hx:t d ≤ N)
    (hA:w*‖alto (Orchard.Path S v) m d‖*(4*(1+(A.B.a.params k).columns)/Bid.gainChart (Orchard.Path S v) k m) ≤ Legato.Bandage.fly A.B.a d m/2)
include hy hw hp hk hA h
variable (hc:GridApprox.room A.B.a J k (lensScope (yard v U) d))
local notation "Ve"=> Size.axis F x
local notation "iT"=> GridApprox.window (0:Site ((yard v U).side k n)) (lensScope (yard v U) d)
include hK hc
lemma chordata (hN:k < N):
   let C:= Cellar.yard v U
   let b:=(U.cantors v d n)
   let P:=b.song N
   let F0:=(frames G).level d
   let M:=Size.axis F0 x
   let l:t d ≤ k:= hp.trans hk
   let Bc:= lens C N k n d M
   let sf:= (Cells.center C.S n (hw.1.trans (hk.trans hN.le)) 0)
   ∃ (Z:∀ i:ℕ, Relay.Solo F0 (Orchard.Path S v) n i),
     Z k=Relay.pair (Orchard.Path S v) N n P (Extra.Histories.primary 0 M) 0 ∧
     Quired (L:=fun i _=>U.paths S v R d n i N) (Orchard.Path S v) N n (hol G) P (t d) k Z (Nat.le_of_lt hN) ∧
       F0.coeffSize (M-(P.tone k).index (Z (t d)).a) ≤ 1/4 ∧ Interior (GridApprox.window (0:Site (C.side k n)) (lensScope C d)) Bc ∧ sf.rootTest (C.beta N n) (GridApprox.backTo C.path N n hN.le Bc- C.O N n ((Cellar.gate v U d N n).terminal (Z (t d)).a) 0) ≤ stakes C J m/w := by
   intro C X P V z l Bc sf; have hx' := l.trans hN.le; have hs:= X.lyr N hx'; let e(i:ℕ) (_:i<N):= U.paths S v R d n i N; have ht:= hs.comes; have hM:= Cellar.intakeV v U
   have hC i (hi:t d ≤ i) (hm:i<N) := (hs.comes i hi hm).1
   obtain ⟨D,g,r,hP,G,hW,hT,hZ⟩:= Lacing.embrace C N k m n d hM w z P (u:=far A.B.a) (ψ:=waybill A.B.a) (φ:=near A.B.a) (δ:=renal A.B.a) (ζ:=Legato.Bandage.fly A.B.a) (D:=Orchard.roof S v) h e (fun i hi hw=> (U.pay v d n i hi).composes N hw) 1 (4*(1+(A.B.a.params k).columns)) hp hk hN.le hs.earned hC (Size.size_axis V x).le (by rw [mul_one]; exact le_rfl) zero_lt_one hy hA
   let n'':=lensScope C d; have hy:Interior (GridApprox.window (0:Site (C.side k n)) n'') Bc:= Vintage.YM.MergeProof.Accent.visible C N k n d _ hM hN.le
   rw [← hT] at hP; refine ⟨G,hW,hZ,hP.bias,hy,?_⟩
   apply Vintage.YM.MergeProof.Accent.quakes (C:=C) _ _ _ _ _ hM _ _ _ h J hK hN hp hk ‹0<w› hP hs.earned hC ?_ hw _ hc hy
   intro v; have HH:= rem_dominated (((hs.earned.head).heard.earns v).2); erw [hs.head] at HH ⊢; apply MergeProof.onRise _ _ _ _ _ _ _ _ HH
end orchestra
end YM.UVExtension.Mast
