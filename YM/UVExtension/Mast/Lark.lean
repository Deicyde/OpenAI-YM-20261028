import YM.UVExtension.Mast.Houses
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
open Relay
local notation "O0"=> (0:Site ((yard v U).side N n))
local notation "X"=> (cantors v U d n)
local notation "C0"=> yard v U
local notation "Φ"=> (C'|>.labels.level d)
lemma chorus (x: ((frames G).level d).Index): ∃ (f:ℕ→∀ i:ℕ, Solo ((frames G).level d) (Orchard.Path S v) n i), ∀ N:ℕ,∀ hN:k<N,
    let z:= Size.axis F x; let U':= lens C' N k n d z; let b:= (f N k0).a; let T:= Cellar.gate v U d N n
    f N k=Relay.pair H N n ((X).song N) (Extra.Histories.primary 0 (Size.axis F x)) 0∧ Quired (L:=fun i _=>paths S v R U d n i N) H N n O! ((X).song N) k0 k (f N) hN.le ∧ (F).coeffSize (z- ((X).song N|>.tone k|>.index b)) ≤ 1/4 ∧ Interior (GridApprox.window 0 (lensScope C' d)) U' ∧ (Cells.center (C').S n (hw.1.trans (hk.trans hN.le)) 0).rootTest ((C').beta N n) (GridApprox.backTo (C').path N n hN.le U' - (C').O N n (T.terminal b) 0) ≤ stakes C' J m/w:=by
    have he (N:ℕ)(hN:k < N):= chordata d m N n U K h hK J k hw x w hy hp hk hA hc hN
    let f (N:ℕ):∀ i:ℕ, Solo ((frames G).level d) (Orchard.Path S v) n i:= if hi:k<N then (he N hi).choose else fun _ => ⟨0, Extra.Histories.primary 0 0,0⟩
    refine ⟨f,fun i hi=>?_⟩; intro z U' b T; unfold b f; simp only [dif_pos hi]; exact (he i hi).choose_spec

structure LatchUp (P:Family G) (k J N n d:ℕ) (hN:J ≤ N)(hk:k ≤ N)(q:ℝ)(f:(P.labels.level d).Index) (v:P.label d): Prop where
    covers : Interior (GridApprox.window 0 (lensScope P d)) (lens P N k n d (Size.axis (P.labels.level d) f))
    gets: ∀ hi:J ≤ N, (Cells.center P.S n hi 0).rootTest (P.beta N n) (GridApprox.backTo P.path N n hk (lens P N k n d (Size.axis (P.labels.level d) f)) - P.O N n (d:=d) v 0) ≤ q

include he
lemma pref (x: ((frames G).level d).Index): ∃ (f:ℕ→ (F).Coeff), UVExtension.Arrives f∧
    ∀ N:ℕ,∀ hN:k < N, LatchUp C' k J N n d (hw.1.trans (hk.trans hN.le)) hN.le (stakes C' J m/w) x (f N) ∧
      (F).coeffSize (Size.axis F x- ((X).song N|>.tone k|>.index ((gate v U d N n).terminal.symm (f N)))) ≤ 1/4 :=by
    obtain ⟨f,hf⟩:= Mast.chorus d m n U K h hK J k hw w hy hp hk hA hc x
    let g N:=(f N k0).a; let G N:= (gate v U d N n).terminal (g N)
    refine ⟨G,?_,fun N hi=>?_⟩
    · apply (((X).chord S v R d n (U.pay v d n) (U.flow d n v B he) (hp.trans hk) (Size.axis F x) f ((eventually_gt_atTop k).mono (fun i hi=> (hf i hi).1)) (fun i hi=> hf i hi|>.2.1) k0 le_rfl (hp.trans hk)).2).copy; filter_upwards [eventually_gt_atTop k] with i hi; exact (congr_arg (fun t=> (t: (F).Coeff≃ₗ[ℂ] (F).Coeff) (g i)) (peak d i n U (hp.trans (hk.trans hi.le)))).symm -- F. parse
    obtain ⟨hV,hR,hE,hp,hK⟩:= hf N hi; refine ⟨⟨hp,fun hi=>hK⟩,?_⟩; rw [show (gate v U d N n).terminal.symm (G N)= _ from (gate v U d N n).terminal.symm_apply_apply (g N)]; exact hE
end orchestra
end YM.UVExtension.Mast
#print axioms YM.UVExtension.Mast.pref
