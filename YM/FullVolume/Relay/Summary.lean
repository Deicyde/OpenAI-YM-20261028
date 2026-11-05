import YM.FullVolume.Relay.Ticket
/-
 Kernel polynomial part true beta expectation. Absolute control on analytic
 parameter width about central trial, without v measuring.
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
open Sever
variable (w₀:ℕ→ I→ℝ) (r:ℕ→ℝ) (w:I→ℝ) (u:ℕ→I→ℝ)
variable {j:ℕ}(hj:j<N) (hp:m ≤ j)
local notation "A_"=> (arena T W N p F m)
local notation "tn"=> FullVolume.Retreat.till L! m p
lemma aperture (n:ℕ) (v₀:ℝ):∃ b:ℝ,0<b∧ b∈Ray.sun∧ |b| *outCharge R T p m n v₀*(FullVolume.Retreat.till L! m p)⁻¹ ≤ 1/2:=by
    let P':= outCharge R T p m n v₀*(tn)⁻¹
    let b:=min 1 (2*(|P'|+1))⁻¹
    have hx:0 < |P'|+1:=by positivity
    have hb:0<b:= lt_min zero_lt_one (by positivity)
    have hp:b ≤ 1:= min_le_left ..; refine ⟨b,hb,abs_le.mp (by rw [abs_of_pos hb]; exact hp),?_⟩ -- spin.Abs.L
    rw [abs_of_pos hb,mul_assoc]; refine le_trans (b:=b*(|P'|+1)) (mul_le_mul_of_nonneg_left ((le_abs_self P').trans (le_add_of_nonneg_right zero_le_one)) hb.le) ?_; have h : b≤ (2*(|P'|+1))⁻¹ := min_le_right ..; exact (mul_le_mul_of_nonneg_right h hx.le).trans_eq (by field_simp)
-- remove assumptions on aperture when not needed
variable {v₀:ℝ}(hz: ∑ i:I,w i*(quoteUnit T j (d i) ‖x i‖+tariffLog T Θ m (Fintype.card I) (u m i)) ≤ v₀)
include hF hk he hP H hz hp
lemma storms (h: Ride T Θ v B d x w₀ r w u N p o m j hj) (hx:∀ i,R.t (d i) ≤ m) (k:B.Mode) (b:ℝ)(hb:b∈Ray.sun)(h0: |b| *outCharge R T p m (Fintype.card I) v₀*(FullVolume.Retreat.till L! m p)⁻¹ ≤ 1/2): PaidBeam (fun s:Ray.sun=> scoreItem T W N p F B d x ℓ o k (Muse.slash b hb s)) ((2* (FullVolume.Retreat.till L! m p)⁻¹)* (outCharge R T p m (Fintype.card I) v₀/Poly.toll w k)):=by
    obtain ⟨ν,hV,hW⟩:= cruise T W N p m haArc F hF Θ v H B d x ℓ o hk he hP w₀ r w u hj hp h hx -- order
    exact payable T W N p m haArc F hF Θ H (hp.trans_lt hj) B d x ℓ o w u ν k hV hW h.positive hz b hb h0
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.storms
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.aperture
