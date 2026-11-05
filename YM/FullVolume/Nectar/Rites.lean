import YM.FullVolume.Nectar.OrbitA
import YM.FullVolume.Nectar.Keys
import YM.FullVolume.Nectar.Bower
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
set_option quotPrecheck false
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {v q d t t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 360000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q"=> A.B.a.budget (m+1)
local notation "Ω"=> A.B.a.clock.hatBeta (m+1)
local notation "β"=> A.B.a.clock.hatBeta m
local notation "S"=> A.B.a.S.side (m+1) n
local notation "α'"=> A.B.a.S.side m n
open Board MergeProof Marker
variable {V I:Type}[Fintype I][Fintype V][DecidableEq V] {W Z:Type} [SeminormedAddCommGroup W][NormedSpace ℝ W]
open Luna Frets Empire Imago
local notation "𝒬" => Board (A:=A) N m n T
-- no x normalization via μ.TV. Markdebt independent N.Level.Layout.M.C. charge norm.Phase variation only in leaves. coefficients via Mark.Currency.Book.Static.
variable {B: Marker.Census V}
section warm
open Jams Luna Frets
variable (Xk:Orchard N m n T B I W)
local notation "Ls"=> D.L (A.B.a.clock.J (m+1))
local notation "Q!"=> R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "Ce"=> fire G Ls β
local notation "Δe"=> thaw G Ls β
variable (f:sun→Board (A:=A) N m n T) {Y:Mist A.B.a m (fire G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)) (thaw G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))}
local notation "Fk"=> fun t:sun=> (f t).val.val
set_option quotPrecheck false
variable (hx: SectorOn (A:=A) (fun t:sun=> (f t).val.val) Y)
local notation "Vt"=>Jams.guitar H hx
local notation "V₀"=>pass_zero (F:=Fk) Y.base.val Y.base.property
local notation "Ht" => fun t:sun=> Jams.gate (Fk) Y t.val
namespace Orchard
variable (r:W) (t₀:sun)
open Imago Mill
-- `Mill.pole` realization even tho pass_zero not Reads.
include H hx
local notation "Mq"=>fun i:I=> Xk.orbit (f tip) r i
local notation "Y₀"=>fun i:I=> leafG (Y.base.val) (Mq i)
local notation "Ve"=> vacation H Xk f hx r
lemma labels (i:I) : (Ve i).pole.crest=(Xk.orbit (f tip) r i).crest:=by
    let Mi:= Mq i; change Mi.turn.support (Rain.initialBed (Fk tip).val Y.base.val)=Mi.turn.support ((Fk tip).val); cases Mi.turn <;> rfl
lemma countN (i:I) : MergeProof.load ((vacation H Xk f hx r i).pole) = MergeProof.load (Xk.orbit (f tip) r i):= by unfold MergeProof.load; rw [labels]; rfl
variable {w:V→ℝ}{u:V→ℝ}(hw:∀ i,0<w i){o:V→ Site (A.B.a.S.side (m+1) n)}{a:ℝ} (hP:Xk.Ensues w o a u) (hr:‖r‖≤1)
open Mallow Lotus Merge
include hw hr hP
local notation "Pz"=>Ve
local notation "Kq"=>fun i=> (Ve i).pole
local notation "Hp"=> H.sight V₀
local notation "z"=> Xk.vitality w
local notation "hR"=>Xk.hat
local notation "m'"=> A.B.a.S.side m n
local notation "S₁"=> A.B.a.clock.op m n
local notation "wT"=> Xk.hat (f tip) r
lemma leaf_mem (i:I): ∃ y∈ (Xk.mode i).val,o y∈ (Ve i).pole.crest:=by
     rw [labels]; obtain ⟨j,hj⟩:= Xk.va i; exact ⟨j,hj,(hP.fee _ _ hr|>.sites i) (mem_image_of_mem o hj)⟩
lemma storage (x:V): Frets.tollS H hx (Xk.vacation H f hx r) (Xk.vitality w) (Xk.qB w) x ≤ u x:=by
   unfold Frets.tollS; simp_rw [countN]; exact hP.bars (f tip) r x hr
section fee
variable (hA:Arrives R.shape A.delay)(hi:(A.B.a.budget m).supportExponent≥100)(hi':(A.B.a.budget (m+1)).supportExponent≥100){M:ℕ} (hc:Extra.Multi.Occupancy ((A.B.a.clock.op m n).ratio.parent ∘ o) M)(ha:0≤a)
include hA hi hi' hc ha
set_option maxHeartbeats 430000 in
lemma bodyV (he:Palette.shipPrice Ls (Empire.stella Q!) β M a): Crew.Pave (Ve) (z):=by
    let Mm:= Pz; let Jg:= A.B.a.clock.J; let A₀(i:I):=(Xk.mode i).val; let V(i:I):=(Mm i).pole; let B₀:=H.sight V₀
    have ht(i):0 ≤ z i:= Menu.timed (wT i) hw
    have hM:= hA _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)|>.1
    obtain ⟨W₀,b,y₁,fy,kp,Yxg₁,p',P',gP,v',q',hB,hX,hN,hu⟩:=hM.2 _ _ _ _ (Opera.protocol A.B H.paid H.earns.conducts.full) _ _ B₀
    let C:= R.expense (Jg (m+1)) (Jg m); let Q':= Q!; have hz:= R.pledging.agenda _ _ (step_paid A.B.a m)
    have hv : (A.B.a.budget m).supportExponent +3 ≤ C.earn:= (Rain.jersey (A:=A) (m:=m)|>.2.2.1).symm ▸ hz.1
    have hE: 4 ≤ Q'.relative:=by change 4 ≤ (Q!).exp+_+_; linarith only [hv,hi,C.worth,C.first,C.second,(Q!).usable,(Q!).pos] -- verify
    have hp:(V₀).val.p=(A.B.a.budget (m+1)):= (V₀).property.1.point
    have hK: (V₀).val.p.B ≤ 2*radiusB β:=by rw [B₀.laws.intake.sizes,B₀.laws.data.funds.length_eq]; exact hB.covers
    refine ⟨ht,Palette.deckPort V B₀ (Xk.vitality w) ht o A₀ hc (fun i _=>leaf_mem H Xk f hx r hw hP hr i) hE (hp ▸ hi') hM.1 hK ha ?_ (Daisy.ribbon (Empire.stella Q') Ls β) he⟩ -- parameter order
    let h:= hP.fee _ (f tip) hr; intro i
    refine Extra.Multi.Budget.mono (h.budget (o i)) (fun j=>?_) (fun j=>?_) le_rfl
    · split
      next=> exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (ht j) (V j|>.profit))
      next=> rfl
    dsimp only; split
    next hk=> rw [if_pos (h.sites _ (mem_image_of_mem o hk))];
              have he: (V j).crest=(wT j).M.crest:=labels H Xk f hx r j
              rw [he,hp,mul_comm]; exact le_rfl
    next=> exact (h.budget ..).1 _
end fee
end Orchard
end warm
end YM.PhysicalNext.Repeat.Muse.Veil
