import YM.FullVolume.Spiral.North
import YM.FullVolume.Spiral.Stone
/- angle true anchors. IF chart present. top rests later. -/
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
variable {q v d t t':ℝ}{N n m k:ℕ}{L:Lyrics R t t}
open UniformSpace FullVolume Paint Paint.Tower
open Luna MergeProof MergeProof.Matric Legato Legato.Bandage.Boutique Next.Foundations Extra.Histories Planned.GuardedAtom Guard
set_option maxHeartbeats 490000
set_option synthInstance.maxHeartbeats 155000
open Graces Circlet Mallow Legato.Bandage Legato.Bandage.Branch
variable (g:G.Simple)(Φ :Plato L q v d t') (T:Tableau q 300)(h:PaysW R.shape v A.delay) (hz:Spire T R.shape (costP X.p D) A.delay) {W: Bid.Worth}{c₁:ℕ→ℝ}(b:Legato.Bandage R c₁ W) {i l r:ℕ} (hr:l ≤ i)(hs:k+3 ≤ A.B.a.clock.J i)
local notation "P!"=> stageP A.B.a (m+1) n
set_option quotPrecheck false
local notation "m'"=> A.B.a.S.side m n
local notation "n'"=> A.B.a.S.side (m+1) n
local notation "W!"=> (Labels.frames G).level k
local notation "κ"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "A!"=> Ticket A N m n
local notation "J_"=> A.B.a.clock.J (m+1)
local notation "L_"=> D.L J_
local notation "p_"=> localSection G k
local notation "y_"=> Next.Foundations.hol G
local notation "vT"=> c₁ J_
local notation "η"=> Doors.rate (L_)
variable {Nt:Bolt A}(hT:Nest R Nt) {H:∀ m, Desk G (A.B.a.S.side m n)}(hH:∀ m,Feeling A m n (H m))
open YM.Source
variable {S:sun→ℕ→∀ p,Shoot.Trail A.B.a p}(U:∀ s:sun,Branch R (S s) N n l) (M:∀ s:sun, TransferData ((Labels.frames G).level k) (A.B.bake.make (S s)) N n)
variable (hm:∀ s h, Piano b (U s) hH hr hs (M s) h)
local notation "ℒ"=> Fin.last N
open Contest
local notation "DY"=> H N
local notation "j!"=> k
local notation "A_"=> stageP A.B.a N n
local notation "q!"=> fun s:sun=> cargo b hH hr hs (U s) (M s) (hm s)
variable (ha: i≤N)
variable {O:Ops L N n}{F:sun→ Contest N n L}
variable (B:Beam (World (O.plan N le_rfl)))(hx:‖B‖≤1)(hv:∀ s:sun,World.ready ((show Home (O.plan N le_rfl) from (F s).chair Φ O (Fin.last N)):Completion (Home (O.plan N le_rfl)))=Beam.read _ s B)
variable (hf:∀ s:sun,(S s) N n N=(F s).trail N)
include Φ hm hH hx hv hf -- hb not yet
include ha hr hs M b
open Paint.Bale
local notation "U!"=> Matric.Coin (W!) (Next.Foundations.hol G) (H N)
local notation "RT"=> fun s:sun=> S s N n N
local notation "HH"=> A.B.a.S.side N n
set_option maxHeartbeats 530000 in
lemma aim (x:(W!).Coeff): PaidBeam (fun v:sun=> ((((q! (Muse.verso v) N).g x):U!):UniformSpace.Completion U!)) (2*Tower.χ W!*‖x‖):=by
   have he s:= (U s).notices hH (hr.trans ha) le_rfl
   let C:= H N; let Y:= Next.Foundations.hol G
   let R:(s:sun)→ Rep G HH:=RT; let Tn:= O.plan N le_rfl; have hk:R=RT:=rfl
   have hy(s): Well (R s) (H N) (Real.sqrt (A.B.a.clock.forcedAllowance N)):= he s
   have ht(s:sun):HasSlots (R s).p (R s).activities:= (U s).slots N (hr.trans ha) le_rfl
   let p(s:sun):= TopY (W!) p_ (R s) (ht s) k x; let M':= fun s:sun=> (hm s ha).choose
   have he(s):= (hm s ha).choose_spec
   have hP(s): (M s).entries N x=p s:=by
        have hx:= (he s).1; have h: (M s).entries=((M' s).draft _).inits := (he s).2.1; rw [h]; change (M' s|>.tone N|>.plays x)=_; rw [show (M' s).tone N= _ from hx]; rfl
   have hu (s:sun): (p s).Format 0 Y C.orient ∧∃ v,(p s).remBound 0 C.orient C.k v:=by
       let H':=(M' s); have hf' (s₁:sun):=(U s₁).sungAt b hH hr hs N ha le_rfl (he s₁)
       have hx:=hf' s|>.earns x; rw [← hP,show (M s|>.entries) = ((M' s).draft _).inits from (he s).2.1]; refine ⟨along_format _ (hy s|>.alongside.sym) hx.1,_,along_bound _ (hy s|>.alongside.sym) ((hy s|>.paid.symm) ▸ (show ((H'.tone N).plays x).remBound 0 (R s) (Real.sqrt (A.B.a.clock.forcedAllowance N)) ((H'.tone N).charge x) from hx.2))⟩
   have hu'(s): Coin.uses ((q! s N).g x)=capture (p s) (Keeper.sufficient (hH N).aboard):=by
       have hV: (R s)=S s N n N:=rfl; let X':=p s
       have hp : (M s|>.entries N x).x=x:=by rw [hP]; rfl
       have he := Branch.capitals b hH hr hs (U s) _ (hm s) N ha le_rfl x; rw [hp] at he; apply he.trans
       rw [hP]; refine Prod.ext rfl ?_; unfold capture; dsimp only; unfold stowK; rw [show cart (R:=(A.B.bake.make (S s)).rep N n N) (Keeper.sufficient ..)=_ from (show cart (R:=(A.B.bake.make (S s)).rep N n N) (Keeper.sufficient ((U s).slots N (hr.trans ha) le_rfl))=cart (R:=(H N).orient) (Keeper.sufficient (hH N).aboard) from rfl)]; congr 1; funext i
       obtain ⟨hQ,v,he⟩:= hu s; exact congr_fun (Rank.Hue.projector (hy s|>.alongside) (p s) he|>.symm) i.val
   obtain ⟨v,hV,hK⟩:= Muse.ores (stageP A.B.a N n) Tn hx hv
   have hb:C.k^2=A.B.a.clock.forcedAllowance N:=by unfold C; rw [ (hH N).physical,Real.sq_sqrt (Extra.Histories.forcedPos ..|>.le)]
   have hω (j:Site HH): SumBudget (fun k=>if j∈ (C.orient.activities.forced k).support then C.orient.p.mass (C.orient.activities.forced k).support (v k) else 0) (C.k^2):=by rw [hb,(hH N).aboard.forced,(hH N).healthy]; exact hV j
   have hx₀(s):R s= (F s).trail N:=hf s
   have hp0:∀ i U,PaidBeam (fun s:sun=>(R s).activities.K i U) (v i):=by intro i W; exact (hK i W).stamp fun s=>by rw [hx₀ s,← (F s).home_observe Φ O N le_rfl]; rfl
   have h': k ≤ A.B.a.clock.J N:= (show k ≤ k+3 from Nat.le_add_right k 3).trans (hs.trans (A.B.a.fits.mono ha))
   have hf: Extra.Histories.fee (W!) C.orient.p ((localSection G k).footprint (0:Site HH)) (Doors.cameras G k) (C.k^2) ≤ C.k:=by rw [hb,(hH N).healthy,(hH N).physical]; exact (b.clock.sequences N k h').receipts n 0
   apply PaidBeam.stamp ((Bale.atrophy C (fun s=> hy s|>.alongside) (hH N|>.aboard) ht _ x Y (Next.Foundations.sound G _) hω hp0 hf (Doors.cameras_ge G k) (fun j U=> Doors.cameras_holds G k _ j 0 U) (fun s=>(hu s).1)).larger ?_)
   · intro s; let v:=verso s; obtain ⟨hF,a,hU⟩:= hu v; exact congr_arg ((↑):U!→ Completion U!) (Coin.noted (Eq.trans (hu' v) (alb_read _ _ _ hF hU|>.symm)))
   exact (mul_le_mul_of_nonneg_left (coreW (W!) x) zero_le_two).trans (by rw [← mul_assoc])
end YM.PhysicalNext.Repeat.Muse.Veil
