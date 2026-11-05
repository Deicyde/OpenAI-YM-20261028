import YM.FullVolume.Reel.Mezzo
import YM.FullVolume.Relay.Many
/-!
 Charge a **Token** from the *same* Choir as produced from the frame. The
 aligned branch keeps φ for output restoration. The unaligned branch takes
 the input ONLY (no claim on opacity estimate after changing layout!); it
 can afford aggregate log+K.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil.Ship
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
variable {v q d t c e t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 410000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "Q₀"=> A.B.a.budget (m+1)
local notation "S"=> A.B.a.S.side (m+1) n
local notation "α'"=> A.B.a.S.side m n
open Board MergeProof Marker
variable {V I:Type}[Fintype I][Fintype V][DecidableEq V]
open Luna Frets Empire Imago Luna.Aank Lotus
open FullVolume.Nectar Menu Accent Extra.Histories Planned.GuardedAtom Motion
open Splint Splint.Center
variable (B:Marker.Census V) (p:Booker A N m n T)(Z:sun→ Booker A N m n T)(o:V→ Site (A.B.a.S.side (m+1) n))
variable {α:sun→ Config G (A.B.a.S.side (m+1) n)→ℂ}{τ:sun→ℂ} {ωs:sun→ Res G (A.B.a.S.side (m+1) n)} {κ:sun→ Res G (A.B.a.S.side m n)}{φ:sun→ Response G (A.B.a.S.side m n)}
variable {M:(s:sun)→I→Leaf (Z s).val.val.val}{y:Site (A.B.a.S.side m n)}{C:I→ℂ}{Q:I→Wing}
abbrev timeK(s:sun): Rep G (A.B.a.S.side m n):= H.moment (Z s).val.val
variable (j:V)(hc:Choir H Z p y α ωs κ v e c I M C Q τ φ)
include hc
local notation "R₁"=> (fun s:sun=> (Z s).val.val.val)
local notation "R₀"=> timeK H Z
local notation "V!"=> ((A.B.a.clock.op m n).ratio.embed y)
local notation "Φ"=> (A.B.a.clock.op m n).ratio
omit hc
private lemma sendS (s:B.Mode)(b:I→ℂ):∑ i,Poly.send s (b i)=Poly.send s (∑ i,b i):=by ext i; rw [Poly.part_sum]; simp_rw [Poly.part_send]; split; rfl; simp
include hc
lemma anchors (hA:o j=(A.B.a.clock.op m n).ratio.embed y) :∃ (M:Ship p Z o B I), Token p Z o M α ωs τ j v∧∀ s i x,M.oweK H p Z o s j i x=κ s i x-hook ((timeK H Z s).activities) ((timeK H Z s).p.threshold) (φ s) i x:=by
    obtain ⟨b,h,hP⟩:=hc.consumes.coins; let U: ArmadaP A N m n T p o B I:= ⟨Q,fun _=> B.fire j,C,fun _=>singleton_nonempty j,fun i=> by rw [show (↑(B.fire j): Finset _)={j} from rfl,Finset.image_singleton,Finset.singleton_subset_iff,hA]; exact (hc.founded i p).2,fun i t=>(hc.founded i t).1⟩
    let p':Ship p Z o B I:=⟨U,M,b,fun s i=>hc.charts i s,hP,hc.hopes⟩
    have hx: OnlyP p Z o p' j:= ⟨fun i=>rfl⟩
    choose a d ha using hc.issued
    refine ⟨p',⟨hx,fun s u=>?_,fun s i u=>?_,?_⟩,fun s i x=> ?_⟩
    · change ∑ i,Poly.send (B.fire j) (prose (M s i) u*C i)=_; rw [sendS]; simp_rw [mul_comm _ (C _)]; exact congr_arg _ ((hasSum_fintype _).unique (ha s|>.lyric u))
    · change ∑ l,Poly.send (B.fire j) (MergeProof.entry (M s l) i u*C l)= _;rw [sendS]; simp_rw [mul_comm _ (C _)]; exact congr_arg _ ((hasSum_fintype _).unique ((ha s).old i u))
    · unfold slot; simp only [hx.targets,↓reduceIte]; exact h -- mass def
    unfold oweK owl; have ht(i): (p'.stamp p Z o s i).s=B.fire j:=rfl;  simp only [hx.targets,  ↓reduceIte]; have hC:=(ha s).grants i x; simp_rw [one_mul] at hC; exact (hasSum_fintype _).unique hC
open Matric
open Push.Local
abbrev still : Motion:= ((1:Signed),false)
-- takes a `still` translation; hull T unchanged on input (output never tested here)
lemma depart (h:y=0):∃ M:Ship p Z o B I, Token p Z o M (fun s=> stepUp Ship.still (o j) (α s)) (fun s=>floatUp Ship.still (o j) (ωs s)) τ j v:=by
     subst y; let e:=Ship.still; let P(t:Booker A N m n T):= alongM t e (o j); let T':=guilder p e (o j); obtain ⟨b,hb,hP⟩:=hc.consumes.coins
     have he : ∀ (t:Booker A N m n T), T'= guilder t e (o j):= fun _=> uniformM ..
     let r:= T' ∘ Q
     have ht(i:I)(z): Wing.labelRoute (P z) (Q i)= r i:= by unfold r; rw [Function.comp_apply,he z]; rfl
     have hh: (A.B.a.clock.op m n).ratio.embed 0=0:= Motion.embed_origin _
     have hR i:(r i).support p.val.val.val=( (Q i).support p.val.val.val ).image (turnSites e.1 (o j)):= by rw [← ht i p]; exact Wing.supRoute (P p) _
     have hy(i:I): o j∈(r i).support p.val.val.val:= by
           have ht:0∈ (Q i).support p.val.val.val:= hh ▸ (hc.founded i p).2
           rw [hR i]; apply (show turnSites e.1 (o j) 0= o j from (by change Lattice.affine e.1 (o j) 0=o j; simp [Lattice.affine])) ▸ Finset.mem_image_of_mem (turnSites e.1 (o j)) ht
     let M'(s:sun)(i:I): Lotus.Leaf (Z s).val.val.val:= Leaf.route (P (Z s)) (M s i)
     let V: ArmadaP A N m n _ p o B I:= {
         track:=r
         mode:=fun _=>B.fire j
         charge:=C
         sizes:=fun _=>singleton_nonempty _
         roots:=fun i=>by change Finset.image o {j} ⊆ _; rw [Finset.image_singleton,Finset.singleton_subset_iff]; exact hy _
         earns:=fun i Z=> by rw [← ht i Z]; exact Wing.fuelRoute (P Z) _ (hc.founded i Z|>.1) }
     have hm(s i): (M' s i).turn=V.track i:=by change Wing.labelRoute _ _=_; rw [hc.charts]; exact ht ..
     have hS i:Feel (fun s:sun=> (M' s i).ingredient) (b i):=by
         have h:= Feel.transit (ContinuousLinearMap.id ℝ ℝ) (pull e.1 (o j)) (hP i) (fun x=> le_of_eq (one_mul ‖x‖).symm) zero_le_one; rw [one_mul] at h; exact h
     let p': Ship p Z o B I:= ⟨V,M',b,hm,hS,hc.hopes⟩
     have hx:OnlyP p Z o p' j:= ⟨fun _=>rfl⟩
     choose a d ha using hc.issued
     refine ⟨p',⟨hx, fun s u=>?_,fun s i U=>?_,?_⟩⟩
     · change ∑ i,Poly.send (B.fire j) (prose (Leaf.route _ (M s i)) u*C i)=_; rw [sendS]; simp_rw [climb_p e (o j) (P (Z s)),mul_comm _ (C _)]; exact congr_arg _ ((hasSum_fintype _).unique ((ha s).lyric (pull _ (o j) u))) -- defeq still
     · obtain ⟨u,rfl⟩:= (puff e (o j)).surjective i
       change ∑ l,Poly.send (B.fire j) (entry (Leaf.route _ (M s l)) _ U*C l)=_; rw [sendS]; simp_rw [climb_entry e (o j) (P (Z s)),mul_comm _ (C _),floatUp, e];simp_rw [Equiv.symm_apply_apply]; exact congr_arg _ ((hasSum_fintype _).unique ((ha s).old u (pull _ (o j) U)))
     unfold slot; simp_rw [hx.targets]; change ∑ i, _ ≤ v; simp only [↓reduceIte]; change ∑ i, (A.B.a.budget (m+1)).mass ((r i).support p.val.val.val) (b i) ≤ v; unfold BudgetPoint.mass; simp_rw [hR,cover_map (turnSites _ _) (turn_sep e.1 (o j))]; exact hb
end YM.PhysicalNext.Repeat.Muse.Veil.Ship
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Ship.anchors
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Ship.depart
