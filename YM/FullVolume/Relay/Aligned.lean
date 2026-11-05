import YM.FullVolume.Relay.UpStep
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
variable (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ) (H:1  ≤  m)
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
variable (hk:PaysW R.kit.shape T.pay R.alloy.delay)(he:Luna.Spire Θ R.kit.shape (Luna.costP R.metals.p R.rolls) R.alloy.delay)(hP:Sav G R.metals.p.profile R.y Θ v R.rolls.L)
variable (j:ℕ)(hj : j  ≤  N)(ht:∀ i, R.t (d i)<j)
variable (hU:∀ i:ℕ,j  ≤  i→ i<N→∀ a:I, o (i+1) a = ((R.alloy.B.a.clock.op i p).ratio.embed (o i a)))
include ht hU hj
local notation "W0"=>fun i=> quoteTop T N (d i) ‖x i‖
local notation "uE"=> fun m i=> quoteInput T m v (d i) ‖x i‖
local notation "uK"=> fun m i=> quoteCert T m Θ v (d i) ‖x i‖
-- W_N fixed. acquire refresh on `φ` from pinnacle.
variable (w:I→ℝ)(hw:∀ i,0<w i){u s c:ℝ}(hN: 1  ≤  N)
local notation "Pβ"=>fun k=> R.alloy.B.a.clock.forcedAllowance k
local notation "PB"=> ((P N).B)
include hP hk he hF hw hN
set_option maxHeartbeats 440000 in
lemma ceiling (hx:∑ i,w i*quoteTop T N (d i) ‖x i‖  ≤  u)(hv:((PB+PB+1:ℕ):ℝ)^4*((Pβ N)+u)  ≤  1)(hd:0 ≤  (R.alloy.B.a.budget N).supportExponent-1)(htB:0  ≤  c)(hg:Repegs (o N) (P N|>.B) w w 2 c B)(hs:0 ≤ s)(hc:c*(Fintype.card I * (Real.exp ((Pβ N)+u)-1))  ≤  s): InAttic T W N p F B d x ℓ o N le_rfl w s:=by
    choose φ hp ht' using fun i=> crowning T W (d i) N p haArc F hF Θ hk he hP (fun _=> x i) (PaidBeam.static (x i)) (ℓ i) ((ht i).trans_le hj) (o N i)
    let θ (s:Ray.sun)(i):=φ i s
    have hv'(s):= orbitZ T W N p F le_rfl s
    unfold InAttic; rw [foilO T W N p F B d x ℓ o]
    refine startup_close (arena T W N p F N) (o N) w w hw (fun s=> (hv' s).1) (seeds T W N p F d x ℓ o) (fun x=> (hv' x).2.1) θ (fun t i=> (ht' i t).2) (fun t i=> (ht' i t|>.1).symm) W0 ?_ (overhead T W N p haArc F hF N hN le_rfl) (fun s i=>?_) (fun x=>(hv' x).2.2) (by unfold pitchDegree; ring) hd hx hv htB hs hg hc
    · intro i; obtain ⟨b,hb,hB⟩:= (hp i).coins; exact ⟨b,(Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_two) (Nat.cast_nonneg _))) (hB j|>.positives))).trans hb,hB⟩
    obtain ⟨k,hk,hv',hT⟩:= visas T W N p N F B d x ℓ o j hj ht hU hj le_rfl s i
    refine ⟨k,hk,hv',fun U=> ((Accent.boot B (arena T W N p F N s) (seeds T W N p F d x ℓ o s) U i).symm.trans ?_)⟩
    rw [foilO T W N p F B d x ℓ o] at hT; exact hT U
omit hw hN
-- purchases gathered at each level. force acceptance.Tech.HasPose. Save argument elaboration.
variable (w':ℕ→ I→ℝ)(r:ℕ→ℝ)
def CloseCap (u s c:ℝ):Prop:= (∑ i,w i*quoteTop T N (d i) ‖x i‖)  ≤  u ∧ ((((P N).B+(P N).B+1:ℕ):ℝ))^4 * (Pβ N+u) ≤ 1 ∧ 0 ≤  c ∧ Repegs (o N) (P N|>.B) w w 2 c B ∧ 0 ≤ s ∧ c*(Fintype.card I * (Real.exp (Pβ N+u)-1))  ≤  s ∧ 0 ≤  (R.alloy.B.a.budget N).supportExponent-1
structure AlignedStep (m:ℕ)(hm:m<N)(c c' t:ℝ)(V:I→ℝ):Prop where
   funds : Fund (T.L.prim N m p hm) Θ c c' T.pay T.pay
   pos :∀ i,0<V i
   occ : Extra.Multi.Occupancy (o m) 1
   foldB : ((∑ i:I,w' (m+1) i*quoteInput T m v (d i) ‖x i‖)+4*r (m+1)) /c' + (∑ i:I, (quoteInput T m v (d i) ‖x i‖)/(V i))  ≤  1/8
   cap : ∃ A0, (∑ i:I,w' (m+1) i*quoteCert T m Θ v (d i) ‖x i‖)  ≤  A0 ∧ ((((R.alloy.B.a.budget m).B+(R.alloy.B.a.budget m).B+1:ℕ):ℝ))^4*((Pβ m+stepNormGas T m (Fintype.card I))+A0)  ≤  1 ∧ t*stepNormLog T m (Fintype.card I)  ≤  r m ∧ t*(Fintype.card I * (Real.exp ((Pβ m+stepNormGas T m (Fintype.card I))+A0)-1))  ≤  r m
   value : 0 ≤ t
   fundsHot : Repegs (o m) (R.alloy.B.a.budget m|>.B) (w' (m+1)) (w' m) 2 t B
set_option maxHeartbeats 440000 in
lemma on_grid (hi:1  ≤  j)(hm: j  ≤  m)(h':m  ≤  N) (Hs:∀ i (h:j  ≤  i), i ≤ N → ∀ k,0<w' i k) (H0:∃ u c, CloseCap T N p B d x o (w' N) u (r N) c) (HP:∀ i:ℕ,j ≤ i→∀ h:i<N,∃ s s' c V, AlignedStep T N p Θ v B d x o w' r i h s s' c V) : InAttic T W N p F B d x ℓ o m h' (w' m) (r m):=by
      induction h' using Nat.decreasingInduction with
      | self=> obtain ⟨u,c,hb,h0,hx,h,hs,hv,hD⟩:=H0; exact ceiling T W N p haArc F hF Θ v B d x ℓ o hk he hP j hj ht hU (w' N) (Hs N hm le_rfl) (hi.trans hj) hb h0 hD hx h hs hv
      | of_succ m hn IH=>
           obtain ⟨s,s',c,V,H⟩:= HP m hm hn; let p:= IH (hm.trans m.le_succ)
           obtain ⟨a,hA,hY,hF',ht'⟩:= H.cap
           exact upStep T W N _ m haArc F hF Θ v (hi.trans hm) hn B d x ℓ o hk he hP j hj ht hU hm _ _ (Hs _ (hm.trans m.le_succ) hn) V H.pos p H.funds H.occ H.fundsHot H.value H.foldB hA hY hF' ht'
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.on_grid
