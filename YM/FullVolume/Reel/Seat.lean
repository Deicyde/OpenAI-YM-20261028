import YM.FullVolume.Reel.Buoy
import YM.FullVolume.Reel.Revive
import YM.FullVolume.Nectar.Bower
/- Harvest. Turns under shared signed-orientation permutation along Book. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
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
variable {v q s t' t t₂:ℝ}{N n m d:ℕ}{L:Lyrics R t t}
open UniformSpace
open Luna Graces Mallow Extra.Histories Planned.GuardedAtom Guard
open MergeProof MergeProof.Matric Next.Foundations
set_option maxHeartbeats 480000
set_option synthInstance.maxHeartbeats 130000
set_option quotPrecheck false
variable (H:Chord R N m n t t) (g:G.Simple)(Z:Ticket A N m n)
local notation "s₀"=> A.B.a.S.side m n
local notation "s₁"=> A.B.a.S.side (m+1) n
variable {W:Bid.Worth}{c₁:ℕ→ℝ}(b:Legato.Bandage R c₁ W) (hd:d+3 ≤ A.B.a.clock.J m)(U0:Heading ((Labels.frames G).level d))(hU:EntryP H b hd U0)
local notation "k₀"=> A.B.a.clock.J m
local notation "k₁"=> A.B.a.clock.J (m+1)
local notation "L_"=> D.L k₁
local notation "ℓ"=> ((L_).val:ℂ)^d
local notation "F_"=> (Labels.frames G).level d
local notation "p_"=>localSection G d
local notation "o_"=>Next.Foundations.hol G
local notation "R_"=> Z.val.val
local notation "κ"=> A.B.a.clock.forcedAllowance m
local notation "va"=> authors A.B.a m
local notation "D_"=> Orchard.portal H Z.val
-- bones Context.N
namespace Splint
open Graces Mallow MergeProof.Menu Circlet Blush Lotus Orchard
open YM.FullVolume.Nectar FullVolume.Ray Luna.Aank FullVolume FullVolume.Paint.Tower Stamp Board ArmadaP
open YM.Source Extra.Histories.Motion
variable {S: Set Wing} {T:Team (stageP A.B.a (m+1) n)}
local notation "X0"=> Booker A N m n T
local notation "Φ"=> (A.B.a.clock.op m n).ratio
variable (p:Booker A N m n T)(v:Motion)(x:Site (A.B.a.S.side (m+1) n))
lemma steward : amid (T.val v.1 x) p.val.val.val.activities v.1 x:=by
    obtain ⟨u,hu⟩:=p.property; rw [hu.bills]; exact u.2.val.property _ _
abbrev alongM : p.val.val.val.activities.Moves v.1 x:= (steward p v x).choose
def guilder := travelW (R:=p.val.val.val) v x (alongM p v x)
local notation "U_"=> framePay (A:=A) (m:=m)
lemma uniformM (u:Booker A N m n T): guilder p v x= guilder u v x:=by
    obtain ⟨hr,hs⟩:=(steward p v x).choose_spec; obtain ⟨ht,hK⟩:=(steward u v x).choose_spec
    apply Equiv.ext; intro i
    change Wing.labelRoute (alongM p v x) i=Wing.labelRoute (alongM u v x) i; cases i <;> unfold Wing.labelRoute; exact congr_arg _ (DFunLike.congr_fun (hr.trans ht.symm) _); exact congr_arg _ (DFunLike.congr_fun (hs.trans hK.symm) _)
variable (U:Desk G (A.B.a.S.side (m+1) n))(he: Legato.Bandage.Boutique.Feeling A (m+1) n U)(K:Keeper U.orient.p U.orient.activities) (hk:K=Keeper.sufficient he.aboard)
def cabin (z:Motion) := guilder p z ((A.B.a.clock.op m n).ratio.embed 0)
def sailsM := ⋃ i:Motion,(cabin p i) '' (inkSet (A:=A) (m:=m) (n:=n) U K)
local notation "D₀"=> inkSet (A:=A) (m:=m) (n:=n) U K
local notation "Xk"=> sailsM p U K
lemma sailsFin : (Xk).Finite:= Set.finite_iUnion (fun j=> (inkFinite U K).image (cabin p j))
include he hk
-- anchoring/birth at any orientation
lemma orbitable (w:Xk)(t:Booker A N m n T): w.val.blank t.val.val.val ∧ 0∈ w.val.support t.val.val.val:=by
    rcases w with ⟨i,hi⟩; obtain ⟨m,r,hr,hi⟩:=mem_iUnion.mp hi
    let v₀:=(Φ).embed 0; let hm:=(alongM t m v₀)
    have hx: 0∈r.support t.val.val.val:= (informed t.val U he K ⟨r,hr⟩).2
    have hF:∀ v',r=v'→ r.blank t.val.val.val:=fun _ _=> (informed t.val U he K ⟨r,hr⟩).1
    have heq: i=Wing.labelRoute hm r:= by change cabin p m r=i at hi; unfold cabin at hi; rw [uniformM p m _ t] at hi; exact hi.symm
    change i.blank _ ∧ 0∈i.support t.val.val.val; rw [heq]; refine ⟨Wing.fuelRoute (alongM t m v₀) _ (hF r rfl),?_⟩
    rw [Wing.supRoute]; have H : v₀=0:=Motion.embed_origin _; rw [H]; exact mem_image.mpr ⟨0,hx,by simp [Lattice.affine]⟩
omit hk he
end Splint
end YM.PhysicalNext.Repeat.Muse.Veil
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Splint.orbitable
