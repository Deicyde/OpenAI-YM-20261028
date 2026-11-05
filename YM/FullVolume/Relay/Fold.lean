import YM.FullVolume.Relay.Post
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
variable (hk:PaysW R.kit.shape T.pay R.alloy.delay)(he:Luna.Spire Θ R.kit.shape (Luna.costP R.metals.p R.rolls) R.alloy.delay)(hP:Sav G R.metals.p.profile R.y Θ v R.rolls.L)
variable (w w':I→ℝ)(hw:∀ i,0<w i) (u u': I→ℝ)(hu: ∀ i,0<u i)
variable {r r' c v₀: ℝ}
-- furl = proceeds from processing level m+1, on natural µ masks and INCLUDING quiet
local notation "tE"=> stepNormLog T m (Fintype.card I)
local notation "tK"=> stepNormGas T m (Fintype.card I)
abbrev Furl (u: I→ℝ)(ν:Ray.sun→I→ℂ):Prop:= ∃ E K, Proceeds (arena T W N p F m) (o m) w E K ν (P m) (Fo m hN.le) tE tK (fun i: I=>tariffLog T Θ m (Fintype.card I) (u i)) (fun i:I=> tariffGas T m (Fintype.card I) (u i))
local notation "o'"=> (Φ).op m p
local notation "om"=> o (m+1)
-- Step costs separated.
variable (hv: Fund (T.L.prim N m p hN) Θ r r' T.pay T.pay)
variable (hO : ((R.alloy.B.a.clock.op m p).ratio.parent ∘ o (m+1))=o m)(hX:Extra.Multi.Occupancy (o m) 1)
variable (ν:Ray.sun→ I→ℂ)
include hw H hu hv hX hO
lemma unaligned
   (Z:Ray.sun→ Booker R.alloy N m p (salons T p N (m+1) hN))(h':Placed T W N p m F H hN Z) (hB:Barge (T.L.prim N m p hN) Z)
   (α:Ray.sun→ I→ Config G ((S).side (m+1) p)→ℂ)(ωs:Ray.sun→ I→ Res G ((S).side (m+1) p))
   (h : Attic B (arena T W N p F (m+1)) (P (m+1)) (o (m+1)) w (Fo (m+1) hN) α ωs (pitchDegree R (m+1)) v₀) (hY:∀ i,∃ (J:Type) (hJ:Fintype J)(M:Ship (Z Jams.tip) Z om B J), Token (Z Jams.tip) Z om M (fun s=> α s i) (fun s=>ωs s i) (fun s=>ν s i) i (u' i))
   (hy : ((∑ i:I,w i*u' i)+4*v₀) /r' + (∑ i:I,u' i/u i)≤1/8): Furl T W N p m F Θ hN B d x ℓ o w u ν:=by
      choose J k mK hm using hY
      let Hq:= T.L.prim N m p hN
      let Y(s:Ray.sun):=(Z s).val
      have hF₀(s):= sameFiber T W N p m F H hN Z h' s
      have hP : arena T W N p F m=timeK (T.L.prim N m p hN) Z:=funext fun s=>(hF₀ s).2.1
      have hF': arena T W N p F (m+1)=fun s:Ray.sun=> (Z s).val.val.val:=funext fun s=>(hF₀ s).1
      obtain ⟨E,K,Yh,hY⟩:=Ship.many Hq Θ T.gains.SimpleR (Z tip) (o (m+1)) w Z hB hw hv (hO ▸ hX) u u' ν (Fo (m+1) hN) α ωs hu hy mK hm (hF' ▸ h) (by unfold pitchDegree; linarith only)
      have htQ: remit Z (Fo (m+1) hN)=Fo m hN.le:=by
        funext s; rw [foilStep T W N p m F B d x ℓ o s hN]; unfold remit; exact congr_arg (fun k=>(R.alloy.B.a.clock.op m p).push k (Fo (m+1) hN s)) (congr_arg Rep.beta (congr_fun hF' s)).symm
      refine ⟨E,K,?_⟩; rw [hP, ← hO,← htQ]; exact Yh
include hF
include hP hk he
local notation "Vw"=>fun i=> quoteInput T m v (d i) ‖x i‖
lemma lastAligned (hU:∀ i,R.t (d i)≤ m)(h: InAttic T W N p F B d x ℓ o (m+1) hN w' v₀) (hM:Repegs (o (m+1)) (R.alloy.B.a.budget (m+1)).B w' w 0 1 B) (ht:∀ i,0<w' i)
    (hy : ((∑ i:I,w i*quoteInput T m v (d i) ‖x i‖)+4*v₀) /r' + (∑ i:I,(quoteInput T m v (d i) ‖x i‖)/u i) ≤ 1/8): ∃ ν, Furl T W N p m F Θ hN B d x ℓ o w u ν ∧ ∀ i,PaidBeam (fun s:Ray.sun=>ν s i) (quoteUnit T m (d i) ‖x i‖):=by
    obtain ⟨Z,hZ,H'⟩:= ancillary T W N p m haArc F hF H hN
    choose J hJ L τ ht' hO' using fun i=> infusion T W N p m haArc F hF Θ v H hN B d x ℓ o hk he hP Z hZ H' hU i
    let ν(s:Ray.sun)(i):=τ i s
    let Y(s:Ray.sun):=(Z s).val; refine ⟨ν,?_, fun i=>hO' i⟩
    have hx:= attic_shrink (arena T W N p F (m+1)) (o (m+1)) w' w ht (show Attic .. from h) hM
    exact unaligned T W N p m F Θ H hN B d x ℓ o w hw u Vw hu hv hO hX ν Z hZ H' _ _ hx (fun i=>⟨J i,hJ i,L i,ht' i⟩) hy
omit hP hk he
-- DESCENT. Multiple repeg still relative to output positions, offshift (t supports in parent). Power eOut−3 >.. . exported recurrence and final stop aperture.
lemma excursion (hN': m+1<N) (h:Furl T W N p (m+1) F Θ hN' B d x ℓ o w u' ν)
     (htB:Repegs (o (m+1)) (R.alloy.B.a.budget (m+1)).B w w 2 c B)(hc:0≤c)(hP₀: c*stepNormLog T (m+1) (Fintype.card I) ≤ v₀)(hz:c*stepNormGas T (m+1) (Fintype.card I) ≤ v₀)(hf:let L i:=2*tariffLog T Θ (m+1) (Fintype.card I) (u' i)+2*tariffGas T (m+1) (Fintype.card I) (u' i)
                         ((∑ i:I,w i*L i)+4*v₀)/r' + (∑ i,L i/(u i)) ≤ 1/8): Furl T W N p m F Θ hN B d x ℓ o w u ν:=by
    obtain ⟨Z,hZ,H'⟩:= ancillary T W N p m haArc F hF H hN
    obtain ⟨E,K,hQ⟩:=h
    have hx := hQ.unaltered (arena T W N p F (m+1)) (o (m+1)) w w hw E K ν (show pitchDegree R (m+1)+2 ≤ (P (m+1)).supportExponent by unfold pitchDegree; linarith) hc htB hP₀ hz
    apply unaligned T W N p m F Θ H hN B d x ℓ o w hw u _ hu hv hO hX ν Z hZ H' _ _ hx _ hf
    have ht : arena T W N p F (m+1) =fun s:Ray.sun=> (Z s).val.val.val:=funext fun s=>(sameFiber T W N p m F H hN Z hZ s).1
    rw [ht] at hQ
    intro i; exact Ship.single (Z Jams.tip) Z (o (m+1)) w i E K ν _ hQ
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.lastAligned
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.excursion
