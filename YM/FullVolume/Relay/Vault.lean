import YM.FullVolume.Relay.Fold
/-
 Roll under unaligned observations with NEW allocations. Keep unit term ν
 throughout. No costs assumed on its size to obtain the pushes; size is
 earned only from initialization at observation. Let posting step below.Stop.
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
variable (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ) (H:1  ≤  m)(hN:m<N)
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
variable (hk:PaysW R.kit.shape T.pay R.alloy.delay)(he:Luna.Spire Θ R.kit.shape (Luna.costP R.metals.p R.rolls) R.alloy.delay)(hP:Sav G R.metals.p.profile R.y Θ v R.rolls.L)
-- full split kernel track valuation. Exposes closure costs.
variable (w₀:ℕ→ I→ℝ) (r:ℕ→ℝ) (w:I→ℝ) (u:ℕ→I→ℝ)
structure Transit (m:ℕ)(h:m<N)(a b:ℝ) :Prop where
   funds :Fund (T.L.prim N m p h) Θ a b T.pay T.pay
   pays : Extra.Multi.Occupancy (o m) 1
   tracks : ((R.alloy.B.a.clock.op m p).ratio.parent ∘ o (m+1))=o m
   positive i:0<u m i
structure Crossing (m:ℕ)(h:m<N):Prop where
   earn : ∃ a b, Transit T N p Θ o u m h a b∧ Repegs (o (m+1)) (R.alloy.B.a.budget (m+1)).B (w₀ (m+1)) w 0 1 B ∧
             ((∑ i:I,w i*quoteInput T m v (d i) ‖x i‖)+4*r (m+1))/b + (∑ i:I,(quoteInput T m v (d i) ‖x i‖)/(u m i))  ≤  1/8
structure Underway (m:ℕ)(h:m<N):Prop where
   earn : ∃ a b c,Transit T N p Θ o u m h a b ∧ Repegs (o (m+1)) (R.alloy.B.a.budget (m+1)).B w w 2 c B ∧ 0 ≤ c ∧ c*stepNormLog T (m+1) (Fintype.card I)  ≤  r (m+1) ∧ c*stepNormGas T (m+1) (Fintype.card I)  ≤  r (m+1) ∧
                              (let L i:=2*tariffLog T Θ (m+1) (Fintype.card I) (u (m+1) i)+2*tariffGas T (m+1) (Fintype.card I) (u (m+1) i); ((∑ i:I,w i*L i)+4*r (m+1))/b+ (∑ i,L i/(u m i))  ≤  1/8)
-- j=index **just below** observation.
structure Ride (N p:ℕ) (o:∀ m,I→ Site (R.alloy.B.a.S.side m p)) (m j:ℕ)(hj:j<N):Prop where
  presses k : j+1  ≤  k→k  ≤  N→∀ i,0<w₀ k i
  occupancy (i:ℕ)(hi:j+1  ≤  i)(ht:i<N): ∀ a:I, o (i+1) a = (R.alloy.B.a.clock.op i p).ratio.embed (o i a)
  top : ∃ a c, CloseCap T N p B d x o (w₀ N) a (r N) c
  surface :∀ i:ℕ,j+1 ≤ i→∀ h:i<N,∃ s s' c V, AlignedStep T N p Θ v B d x o w₀ r i h s s' c V
  positive i:0 < w i
  bridge : Crossing T N p Θ v B d x o w₀ r w u j hj
  left i : m ≤ i→∀ h:i<j, Underway T N p Θ B o r w u i (h.trans hj)
variable {j:ℕ}(hj:j<N) (hp:m  ≤  j)
include hF hk he hP H hp
local notation "Y_"=> Furl T W N p m F Θ
lemma cruise (h: Ride T Θ v B d x w₀ r w u N p o m j hj) (hx:∀ i,R.t (d i) ≤  m) : ∃ ν, Furl T W N p m F Θ (hp.trans_lt hj) B d x ℓ o w (u m) ν ∧ ∀ i,PaidBeam (fun s:Ray.sun=>ν s i) (quoteUnit T j (d i) ‖x i‖):=by
     let j':= j+1
     have hi:=H.trans hp
     have ht i: R.t (d i)  ≤  j:= (hx i).trans hp
     have hO := on_grid T W N p j' haArc F hF Θ v B d x ℓ o hk he hP j' hj (fun i=> Nat.lt_succ_of_le (ht i)) h.occupancy w₀ r (by unfold j';omega) le_rfl hj h.presses h.top h.surface -- incl W.F.
     obtain ⟨a,b,hV,hT,hB⟩:= h.bridge.earn
     obtain ⟨ν,hY,Hz⟩:= lastAligned T W N p j haArc F hF Θ v hi hj B d x ℓ o hk he hP w (w₀ j') h.positive (u j) hV.positive hV.funds hV.tracks hV.pays ht hO hT (h.presses j' le_rfl hj) hB
     refine ⟨ν, ?_,Hz⟩
     -- induction from j downward leaving costs referenced to fixed j. (Do not take new assembly partner)
     have hm (i:ℕ)(hl:m  ≤  i) (hx:i  ≤  j) : Furl T W N p i F Θ (hx.trans_lt hj) B d x ℓ o w (u i) ν:=by
         induction hx using Nat.decreasingInduction with
         | self=> exact hY
         | of_succ i hi IH=>
             obtain ⟨a,b,c,hC,htK,hc,hB,hK,hM⟩:= (h.left i hl hi).earn
             exact excursion T W N p i haArc F hF Θ (H.trans hl) (hi.trans hj) B d x ℓ o w h.positive (u i) (u (i+1)) hC.positive hC.funds hC.tracks hC.pays ν (show i+1<N from (show i+1  ≤  j from hi).trans_lt hj) (IH (hl.trans i.le_succ)) htK hc hB hK hM
     exact hm _ le_rfl hp
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.cruise
