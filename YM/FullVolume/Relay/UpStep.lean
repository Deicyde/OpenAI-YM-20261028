import YM.FullVolume.Relay.Foil
/-
 Recurrence on aligned descent. Integrates the analytic Ribbon estimates at
 multiweight. Keep exact Ram.press claims. τ (Mach unit at kernel-free masks)
 may reset on this portion; not in Roll-ups below observation j.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign.Face
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} (T:Campaign R) (W:Pillars R T)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
open Spirit Branch
open Boutique Guard
open Extraction Extraction.Lease
variable (N p m:ℕ)
open UniformSpace
variable {a:ℝ}(haArc:a∈ Ray.sun)
variable (F:Ray.sun→ Face T W)(hF:∀ s:Ray.sun, Face.evalV T W (F s) p N= ask R.alloy.B.a (slash a haArc s).val)
open Veil.Splint Roof.Chord Jams FullVolume.Nectar
local notation "Vt"=>T.gains
local notation "Φ"=> R.alloy.B.a.clock
local notation "Z₁"=>fun s:Ray.sun=> (F (Muse.verso s)).score
local notation "Xo"=>fun s:Ray.sun=> (F (Muse.verso s)).owns
local notation "Wν"=> (R.tuning.receipts)
local notation "P"=>R.alloy.B.a.budget
local notation "R₁"=> arena T W N p F
variable (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ) (H:1 ≤ m)(hN:m<N)
local notation "h_"=> (T.L.prim N m p hN)
variable {I:Type}[Fintype I] [DecidableEq I](B: Marker.Census I)
open Marker
variable (d:I→ℕ)(x: (i:I)→ ((Labels.frames G).level (d i)).Coeff)(ℓ:I→Motion)
local notation "Xc"=>fun s:Ray.sun=>(F (Muse.verso s)).score
local notation "ζ"=> fun s:Ray.sun=> (F (Muse.verso s)).owns
local notation "C"=> fun s:Ray.sun=> R.alloy.B.bake.make (Xc s|>.q)
local notation "S"=> R.alloy.B.a.S
variable (o: ∀ m:ℕ,I→ Site (R.alloy.B.a.S.side m p))
local notation "Fo"=> foils T W N p F B d x ℓ o
open MergeProof.Accent
local notation "Q_"=> Fintype.card I
local notation "FrE"=> fieldLog T W N p F d x ℓ o
local notation "FrK"=> fieldForce T W N p F d x ℓ o
local notation "FrD"=> fieldDensity T W N p F d x ℓ o
abbrev stepNormLog (T:Campaign R)(k n:ℕ):ℝ:= groupBillE G T.width n (R.rolls.L (R.alloy.B.a.clock.J (k+1))) (R.alloy.B.a.clock.hatBeta k)
abbrev stepNormGas (T:Campaign R)(k n:ℕ):ℝ:= groupBillK G T.width n (R.rolls.L (R.alloy.B.a.clock.J (k+1))) (R.alloy.B.a.clock.hatBeta k) (R.kit.shape.μ (R.alloy.B.a.clock.J (k+1)) (R.alloy.B.a.clock.J k))
abbrev tariffLog (T:Campaign R)(Θ:Luna.Tableau T.width 300) (k n:ℕ) (u:ℝ):ℝ:= singleBillE T.width Θ n (R.rolls.L (R.alloy.B.a.clock.J (k+1))) u
abbrev tariffGas (T:Campaign R)(k n:ℕ) (u:ℝ):ℝ:=singleBillK T.width n ((R.alloy.B.a.clock).forcedAllowance k) u
abbrev quoteTop (d:ℕ)(z:ℝ):ℝ:= ‖mintT T d N‖*(Real.exp ((P N).supportExponent+2) *(fullCost ((Labels.frames G).level d) (P N) (Doors.cameras G d)* (χ ((Labels.frames G).level d)))* (z*Real.exp (R.alloy.B.a.S.scale N-R.alloy.B.a.S.scale (R.t d))))
abbrev pitchDegree (R:Run G)(m:ℕ):= (R.alloy.B.a.budget m).supportExponent-3
abbrev InAttic (j:ℕ)(hj:j ≤ N)(w:I→ℝ)(t:ℝ): Prop:= Attic B (arena T W N p F j) (P j) (o j) w (Fo j hj) (FrE j) (FrK j) (pitchDegree R j) t
variable (hk:PaysW R.kit.shape T.pay R.alloy.delay)(he:Luna.Spire Θ R.kit.shape (Luna.costP R.metals.p R.rolls) R.alloy.delay)(hP:Sav G R.metals.p.profile R.y Θ v R.rolls.L)
variable (j:ℕ)(hj : j ≤ N)(ht:∀ i, R.t (d i)<j)
variable (hU:∀ i:ℕ,j ≤ i→ i<N→∀ a:I, o (i+1) a = ((R.alloy.B.a.clock.op i p).ratio.embed (o i a)))
include ht hU hj
variable (hm:j ≤ m)
-- current position.at EACH orientation REAL all V.
include hm
lemma visas (hv:m ≤ N)(s:Ray.sun)(i:I): ∃ k:ℕ→ Config G (R.alloy.B.a.S.side m p)→ℂ, Dominated k ∧ fieldForce T W N p F d x ℓ o m s i=profile (arena T W N p F m s|>.activities) k ∧ ∀ U,(foils T W N p F B d x ℓ o m hv s U).part (B.fire i)= Accent.coin (arena T W N p F m s) (fieldLog T W N p F d x ℓ o m s i) k U:=by
     let u:=d i; obtain ⟨k,hk,hv',h'⟩:= revenueP T W u N p F (fun _=>x i) (ℓ i) m ((ht i|>.le).trans hm) hv (o m i) s
     refine ⟨k,hk,hv'.symm,fun U=> (congr_fun (foilFire T W N p F B d x ℓ o j hj ht hU m hm hv s i) U).trans (congr_fun h' U)⟩
variable (w w':I→ℝ)(hw:∀ i,0<w i) (u:I→ℝ)(hu:∀ i,0<u i)
variable {r r' A0 s s' c:ℝ}
local notation "tE"=> stepNormLog T m (Fintype.card I)
local notation "tK"=> stepNormGas T m (Fintype.card I)
local notation "QP"=> ((P m).B)
local notation "X!"=> (R.alloy.B.a.clock.op m p).ratio.parent ∘ o (m+1)
local notation "Pβ"=> (Φ).forcedAllowance m
include hF hP hk he hw
include hu H
set_option maxHeartbeats 650000 in
lemma upStep (h:InAttic T W N p F B d x ℓ o (m+1) hN w s) (hv: Fund (T.L.prim N m p hN) Θ r r' T.pay T.pay) (hx:Extra.Multi.Occupancy (o m) 1) (ha: Repegs (o m) (R.alloy.B.a.budget m).B w w' 2 c B) (hd:0 ≤ c)
    (hy:((∑ i:I,w i*quoteInput T m v (d i) ‖x i‖)+4*s) /r' + (∑ i:I, (quoteInput T m v (d i) ‖x i‖)/(u i)) ≤ 1/8) (hp:∑ i:I,w i*quoteCert T m Θ v (d i) ‖x i‖ ≤ A0)
    (hb:(((QP + QP +1:ℕ):ℝ))^4*((Pβ+tK)+A0) ≤ 1) (hα:c*tE≤ s') (hz:c*(Fintype.card I*(Real.exp ((Pβ+tK)+A0)-1)) ≤ s'): InAttic T W N p F B d x ℓ o m hN.le w' s':=by
    obtain ⟨Z,hZ,H0⟩:= ancillary T W N p m haArc F hF H hN
    let w_i i:= quoteInput T m v (d i) ‖x i‖
    let w_k i:= quoteCert T m Θ v (d i) ‖x i‖
    let L:= T.L.prim N m p hN
    choose J hJ M T' Ψ hq hB hν hϵ hX using fun i=> certificate T W (d i) N p m haArc F hF Θ v H hN Z B (x i) (ℓ i) hk he hP hZ H0 (o (m+1)) (o m i) i ((ht i|>.le).trans hm) (hU m hm hN i|>.symm)
    let o':=o (m+1); let U(s:Ray.sun)(i):= T' i s
    let j₀:= Z Jams.tip; let v₀(s:Ray.sun)(i):= Ψ i s
    have hyi(i):Token j₀ Z o' (M i) (fun s=> FrE (m+1) s i) (fun s=> FrK (m+1) s i) (fun s=>U s i) i (w_i i):=hq i
    have hQ (s:Ray.sun):=(sameFiber T W N p m F H hN Z hZ s); have hF₀:((Φ).op m p).ratio.parent ∘ o'=o m:=by funext i; dsimp only [Function.comp_apply,o'];rw [hU _ hm hN]; exact Ratio.embed_parent ..
    have h' : arena T W N p F (m+1)=fun s:Ray.sun=>(Z s).val.val.val:=funext (fun s=> (hQ s).1)
    have h0 : arena T W N p F m = timeK (T.L.prim N m p hN) Z:= funext (fun s=> (hQ s).2.1)
    obtain ⟨E,K,hK,hT⟩:= Ship.many L Θ T.gains.SimpleR (Z tip) o' w Z H0 hw hv (hF₀ ▸ hx) u w_i U (Fo (m+1) hN) (FrE (m+1)) (FrK (m+1)) hu hy M hyi (h' ▸ (show Attic .. from h)) (by unfold pitchDegree; linarith only)
    let P' := P m; have hr:(R.alloy.B.a.budget m).supportExponent-1=pitchDegree R m+2:=by unfold pitchDegree; ring
    have htQ: remit Z (Fo (m+1) hN)=Fo m hN.le:=by
        funext s; rw [foilStep T W N p m F B d x ℓ o s hN]; unfold remit; exact congr_arg (fun k=>(R.alloy.B.a.clock.op m p).push k (Fo (m+1) hN s)) (congr_arg Rep.beta (congr_fun h' s)).symm -- dependent beta eq issue
    have hK' : Proceeds (arena T W N p F m) (o m) w E K U (P m) (Fo m hN.le) (tE) (tK) (fun i=>tariffLog T Θ m (Fintype.card I) (u i)) (fun i=> tariffGas T m (Fintype.card I) (u i)):=by rw [← htQ,h0, ← hF₀]; exact hK
    have hq k:=(orbitZ T W N p F hN.le k)
    refine attic_close (arena T W N p F m) (o m) w w' hw (fun s=> (hq s).1) E K (hK'.realP) v₀ ?_ ?_ (fun i=> hK'.ledger i) w_k (fun i=>hB i) (overhead T W N p _ F hF m H hN.le) hK'.bondK hK'.contact (fun s=>(hq s).2.1) (fun s i=> visas T W N p m F B d x ℓ o j hj ht hU hm hN.le s i) (fun s U=> (hq s).2.2 U) hr (by linarith only [hv.rooms.support]) hp hb hd ha hα hz
    · exact fun s i=> hϵ i s
    intro s i j U; rw [hT]; exact hX i s j U
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.upStep
