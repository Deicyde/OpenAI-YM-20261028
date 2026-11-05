import YM.FullVolume.Reel.Pinnacle
import YM.FullVolume.Relay.Pulse
/-!
 Dossiers on the actual Wilson Face (real diameter). Complete RESTORE proof
 follows on aligned descent using these and an analytic budget calendar.
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
variable (d N p m:ℕ)
open UniformSpace
variable {a:ℝ}(ha:a∈ Ray.sun)
variable (F:Ray.sun→ Face T W)(hF:∀ s:Ray.sun, Face.evalV T W (F s) p N= ask R.alloy.B.a (slash a ha s).val)
open Veil.Splint Roof.Chord Jams FullVolume.Nectar
local notation "Vt"=>T.gains
local notation "Φ"=> R.alloy.B.a.clock
local notation "Z₁"=>fun s:Ray.sun=> (F (Muse.verso s)).score
local notation "Xo"=>fun s:Ray.sun=> (F (Muse.verso s)).owns
local notation "Wν"=> (R.tuning.receipts)
local notation "P"=>R.alloy.B.a.budget
-- Frame apertures.
abbrev arena (j:ℕ)(s:Ray.sun) : Rep G (R.alloy.B.a.S.side j p):= traceH T W N p F s j
local notation "R₁"=> arena T W N p F
variable (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ) (H:1 ≤ m)(hN:m<N)
lemma orbitZ {j:ℕ}(hj:j≤N)(s:Ray.sun) : (arena T W N p F j s).p=P j ∧ (arena T W N p F j s).activities.Valid (P j) ((Φ).allowance j) ((Φ).forcedAllowance j)∧∀ U,(arena T W N p F j s).eval U ≠ 0:=by
    let Q':= (F (Muse.verso s)).score.mat N p; let A:= R.alloy.B.bake.make ((F (Muse.verso s)).score.q); have he:= Q'.choice.represents N p j hj; let v:=A.rep N p j
    exact ⟨he.vac,he.vac ▸ he.good.labels,fun U=>(Tour.bright A Q'.choice N p j hj U).ne'⟩
local notation "h_"=> (T.L.prim N m p hN)
variable (Z:Ray.sun→ Booker R.alloy N m p (salons T p N (m+1) hN))
-- avoid changing hm via cost
abbrev Placed (Z:Ray.sun→ Booker R.alloy N m p (salons T p N (m+1) hN)):Prop:=∀ i:Ray.sun, (Z i).val= Vot ((F (Muse.verso i)|>.score).mat N p|>.steps m H hN)
include hF
lemma ancillary :∃ (Z:Ray.sun→ Booker R.alloy N m p (salons T p N (m+1) hN)), Placed T W N p m F H hN Z ∧ Barge (T.L.prim N m p hN) Z:=by
    obtain ⟨Z,hZ,y,B,hy,hp,hx,hY,hB⟩:=glenoid T W N p m ha F hF H hN; exact ⟨Z,hZ,fun s=>(sameFiber T W N p m F H hN Z hZ s).2.2,y,B,hy,hp,hx,hY,hB⟩
lemma overhead (j:ℕ)(hv:1 ≤ j)(hp:j≤N): WindowP (visaK (arena T W N p F j)) Prod.fst (P j|>.B) ((P j).supportExponent) ((Φ).forcedAllowance j) :=by
    have he:1/2*a∈ Ray.sun:=by obtain ⟨h,hv⟩:=ha; constructor<;> linarith only [h,hv]
    let C (s:Ray.sun):= (F (Muse.verso s)).F p N; let O:= halls T p N
    have hX(i:Ray.sun): (C i).bonusB=ask R.alloy.B.a (slash (1/2*a) he i|>.val):=by rw [show (C i).bonusB= _ from hF (Muse.verso i)]; apply congr_arg; change _*(1/2)*_= _; change i.val*(1/2)*a=i.val*(1/2*a); ring
    let i:Fin (N+1):= ⟨j,hp.trans_lt N.lt_succ_self⟩
    obtain ⟨B,hB,hq⟩:= Veil.terrace T.gains O C he hX i
    let u(s:Ray.sun):= Contest.chair T.gains O (C s) i
    have hh(s): Urns.observe (salons T p N j hp) (u s)=(arena T W N p F j s).activities:= ((C s).home_observe T.gains O j hp).trans (congr_arg Rep.activities (((F (Muse.verso s)|>.score).palm N p (hv.trans hp) j hv hp).symm))
    have ht:= Muse.ex_profile (stageP (L!) i p) (O.plan i (headB i)) (X:=u) hB hq -- implicit F.K.Stage
    dsimp only at ht; rw [show visaK (arena T W N p F j)=(fun s:Ray.sun=> profile (Urns.observe (salons T p N j hp) (u s)) (fun a=>Complex.ofReal ∘ ((Urns.observe (salons T p N j hp) (u s)).K a))) from funext fun s=> by rw [hh] ]; exact ht
-- costs expose. independent of art and roster. Pays fixed ℓ.Photo.Pose.Info.
local notation "F₀"=> ((Labels.frames G).level d)
local notation "P₁"=>R.rolls.L ((Φ).J (m+1))
local notation "η"=> Doors.rate (P₁)
abbrev upFactor (d z) := z*Real.exp (R.alloy.B.a.S.scale (m+1)-R.alloy.B.a.S.scale (R.t d))
abbrev upColumn (i:(Labels.frames G|>.level d|>.Index)):=v d ((Φ).J (m+1))*‖Size.axis (F₀) i‖
abbrev quoteInput (d:ℕ)(z:ℝ):ℝ:= 2*(‖mintT T d (m+1)‖*(upFactor (R:=R) m d z* priceE ((Labels.frames G).level d) (framePay (A:=R.alloy) (m:=m)) (upColumn (R:=R) d m v)))
abbrev quoteCert (d:ℕ)(z:ℝ):ℝ:= ‖mintT T d m‖*(upFactor (R:=R) m d z * priceK Θ.price (R.y ((Φ).J (m+1))) (Doors.rate (P₁)) (P₁) ((Labels.frames G).level d) (upColumn (R:=R) d m v))
abbrev quoteUnit (d:ℕ)(z:ℝ):ℝ:= ‖mintT T d (m+1)‖*upFactor (R:=R) m d z
variable {I:Type}[Fintype I] [DecidableEq I](B: Marker.Census I)
open Marker Center
-- plank.
variable (x: ((Labels.frames G).level d).Coeff)(ℓ:Motion)
   (hk:PaysW R.kit.shape T.pay R.alloy.delay)(he:Luna.Spire Θ R.kit.shape (Luna.costP R.metals.p R.rolls) R.alloy.delay)(hP:Sav G R.metals.p.profile R.y Θ v R.rolls.L)
variable (hZ:Placed T W N p m F H hN Z) (hB:Barge (T.L.prim N m p hN) Z)
abbrev frmE (ℓ:Motion)(j:ℕ)(y:Site (R.alloy.B.a.S.side j p))(s:Ray.sun) : Config G (R.alloy.B.a.S.side j p)→ℂ:=musicE T W d N p F (fun _=> x) ℓ s j y
abbrev frmK (ℓ:Motion)(j:ℕ)(y:Site (R.alloy.B.a.S.side j p))(s:Ray.sun) : Res G (R.alloy.B.a.S.side j p):=musicK T W d N p F (fun _=> x) ℓ s j y
abbrev frmD (ℓ:Motion)(j:ℕ)(y:Site (R.alloy.B.a.S.side j p))(s:Ray.sun) : Config G (R.alloy.B.a.S.side j p)→ℂ:=musicD T W d N p F (fun _=> x) ℓ s j y
variable (o:I→ Site (R.alloy.B.a.S.side (m+1) p))(o₀:Site (R.alloy.B.a.S.side m p))(i:I)
local notation "tK"=>arena T W N p F
include hF hB hZ hk he hP
local notation "dt"=> R.t d
variable (hD:R.t d ≤ m)
include hD
-- publication aligned.Source X/y fixed.M.
set_option maxHeartbeats 440000 in
lemma certificate (ht:((Φ).op m p).ratio.embed o₀=o i): ∃ (J:Type) (h:Fintype J)(M:Ship (Z Jams.tip) Z o B J)(τ:Ray.sun→ℂ)(Ψ:Ray.sun→Response G (R.alloy.B.a.S.side m p)),
       Token (Z Jams.tip) Z o M (frmE T W d N p F x ℓ (m+1) (o i)) (frmK T W d N p F x ℓ (m+1) (o i)) τ i (quoteInput T m v d ‖x‖) ∧ Treasure (fun i'=> Real.exp ((P m).supportExponent *coverNumber (P m).B i')) Ψ (quoteCert T m Θ v d ‖x‖) ∧ PaidBeam τ (quoteUnit T m d ‖x‖) ∧ (∀ s:Ray.sun,∃ t, Attainment (P m) o₀ (Ψ s) t) ∧ ∀ s j u, M.oweK (T.L.prim N m p hN) (Z Jams.tip) Z o s i j u+hook ((arena T W N p F m s).activities) (P m).threshold (Ψ s) j u= frmK T W d N p F x ℓ m o₀ s j u:=by
       obtain ⟨y,B',hy,h,hX,hB,hv⟩:=hB.itinerary
       obtain ⟨J,hJ,M,C,Q,τ,Ψ,hq⟩:=salaries T W d N p m ha F hF Θ hk he hP H hN Z hZ hD (fun _=>x) (PaidBeam.static x) y B' hy h hX (hB.trans (by norm_num)) hv ℓ o₀
       obtain ⟨U,hU,hV⟩:= anchors (T.L.prim N m p hN) B (Z Jams.tip) Z o i hq ht.symm
       choose t u ht' using hq.issued
       have hc(s:Ray.sun): Ship.timeK (T.L.prim N m p hN) Z s= arena T W N p F m s:= (sameFiber T W N p m F H hN Z hZ s).2.1.symm
       have hp(s): (Ship.timeK (T.L.prim N m p hN) Z s).p=P m:= (congr_arg Rep.p (hc s)).trans (orbitZ T W N p F hN.le s).1
       refine ⟨J,hJ,U,τ,Ψ, ?_, ?_,hq.hue,fun s=>⟨_,hp s ▸ (ht' s).cost⟩,fun s j u=>?_⟩
       · change Token _ _ o U _ _ _ _ _ at hU; rw [ht] at hU; exact hU
       · obtain ⟨b,hb,hQ⟩:=hq.coat.coins; refine ⟨b,?_,hQ⟩; refine (Finset.sum_le_sum (fun i _=>?_)).trans hb; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_two) (Nat.cast_nonneg _))) (hQ i).positives
       rw [hV, hp s,hc]; exact sub_add_cancel ..
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.certificate
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.overhead
