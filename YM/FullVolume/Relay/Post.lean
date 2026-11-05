import YM.FullVolume.Relay.Aligned
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
variable (hk:PaysW R.kit.shape T.pay R.alloy.delay)(he:Luna.Spire Θ R.kit.shape (Luna.costP R.metals.p R.rolls) R.alloy.delay)(hP:Sav G R.metals.p.profile R.y Θ v R.rolls.L)
open Push.Local
-- shift at ONE explicit observation k; post pulse unaligned may ignore χ but maintains anchor geometry through `.parent`.
set_option maxHeartbeats 440000 in
private lemma squareK (u:Box ((S).side (m+1) p)) (ℓ:Motion)(i:Site ((S).side (m+1) p)) : puff Ship.still i (puff ℓ 0 u)=puff ℓ i u:=by
    have he(s): sky Ship.still i (sky ℓ 0 s)=sky ℓ i s:=by
        simp_rw [MergeProof.shading, Finset.image_image]; apply Finset.image_congr; intro x _
        change Lattice.affine (1:Signed) i (Lattice.affine ℓ.1 0 x)= Lattice.affine ℓ.1 i x
        simp [Ship.still,Lattice.affine] -- check
    exact Prod.ext (he u.1) (he u.2)
private lemma reexpress (ℓ:Motion)(i:Site ((S).side (m+1) p)) (f : Res G ((S).side (m+1) p))(k:ℂ): floatUp Ship.still i (k • floatUp ℓ 0 f)= k • floatUp ℓ i f:=by
     funext j U; obtain ⟨j,rfl⟩:=(puff ℓ i).surjective j
     have hb(u:Config G ((S).side (m+1) p)):pull ℓ.1 0 (pull (1:Signed) i u)= pull ℓ.1 i u:=by rw [pull_pull]; simp [Lattice.affine]
     unfold floatUp stepUp; dsimp only [Pi.smul_apply]; rw [(puff ℓ i).symm_apply_apply, ← squareK (R:=R) p m, Equiv.symm_apply_apply,Equiv.symm_apply_apply, hb]; rfl -- check
variable (Z:Ray.sun→ Booker R.alloy N m p (salons T p N (m+1) hN)) (h:Placed T W N p m F H hN Z)(hB:Barge (T.L.prim N m p hN) Z)
variable (ht: ∀ i, R.t (d i) ≤ m)
include hF hk he hP h hB ht
local notation "op₀"=> (Φ).op m p
local notation "ε!"=> quoteInput T m v
local notation "r!"=> quoteUnit T m
lemma infusion (i:I):∃ (J:Type) (ha:Fintype J)(M:Ship (Z Jams.tip) Z (o (m+1)) B J)(τ:Ray.sun→ℂ), Token (Z Jams.tip) Z (o (m+1)) M (fun s=> fieldLog T W N p F d x ℓ o (m+1) s i) (fun s=> fieldForce T W N p F d x ℓ o (m+1) s i) τ i (quoteInput T m v (d i) ‖x i‖) ∧ PaidBeam τ (quoteUnit T m (d i) ‖x i‖):=by
     obtain ⟨y,B',hy,h₀,hx,hV,hY⟩:= hB.itinerary
     obtain ⟨I,hI,M,c,S₀,τ,Ψ,H'⟩:= salaries T W (d i) N p m haArc F hF Θ hk he hP H hN Z h (ht i) (fun _=>x i) (PaidBeam.static _) y B' hy h₀ hx (hV.trans (by norm_num)) hY (ℓ i) 0
     obtain ⟨L,ht⟩:= Ship.depart (T.L.prim N m p hN) B (Z Jams.tip) Z (o (m+1)) i H' rfl
     let f(s: Ray.sun) := fieldLog T W N p F d x ℓ o (m+1) s i; let g(s:Ray.sun):= fieldForce T W N p F d x ℓ o (m+1) s i
     let yp:= o (m+1) i
     have he0: ((Φ).op m p).ratio.embed 0=0:= Motion.embed_origin _
     have hp(u: Config G ((S).side (m+1) p)): pull (ℓ i).1 0 (pull Ship.still.1 yp u)= pull (ℓ i).1 yp u :=by rw [pull_pull]; simp [Ship.still, Lattice.affine]
     let u' (s:Ray.sun): Config G ((S).side (m+1) p)→ℂ:= stepUp Ship.still yp (musicE T W (d i) N p F (fun _=>x i) (ℓ i) s (m+1) ((op₀).ratio.embed 0)); let t(s:Ray.sun) := floatUp Ship.still yp (musicK T W (d i) N p F (fun _=> x i) (ℓ i) s (m+1) ((op₀).ratio.embed 0))
     have hh : u'=f:=by
         funext s u; unfold u' f fieldLog frmE musicE; rw [he0]; unfold radiant stepUp; dsimp only [Pi.smul_apply]; rw [hp]; rfl
     have hK : t=g:=by
         funext s j V; unfold g fieldForce frmK musicK; unfold t musicK; rw [he0]
         exact congr_fun (congr_fun (reexpress (R:=R) p m (ℓ i) yp _ _) j) V
     refine ⟨I,hI,L,τ,(congr_arg₂ (fun E K=> Token (Z Jams.tip) Z _ L E K τ i _) hh hK).mp ht,H'.hue⟩
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.infusion
