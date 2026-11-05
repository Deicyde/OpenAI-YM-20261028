import YM.FullVolume.Panel.Uprise
import YM.FullVolume.Panel.RockyR
import YM.MergeProof.Rocky
import YM.MergeProof.Thimble



set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Circlet
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury Graces
open Planned.PrimaryIntegral295 WaterLevels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{M : Metals G}{D:Rolls M.p}{A:Alloy M D}{Q:ℕ→ℕ→ Teller G}{C: Programs M.p}
   {r p:ℕ→ℕ} {R:ℕ→ℕ→Record}{B:Factor A}{V:Bolt A} {meshT:ℕ→∀ p,Trail A.B.a p}
local notation "cc"=> A.B.a
variable {m N n d:ℕ} (hm:m<N)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T"=> A.B.a.clock.J m
local notation "B₁"=> A.B.a.budget m
local notation "B₂"=> A.B.a.budget (m+1)
local notation "X"=> A.B.a.clock.op m n
local notation "V0"=> ships A.B N m n
local notation "V1"=> forecast V m N n
local notation "L"=> D.L J
local notation "y"=> A.B.a.clock.hatBeta m
local notation "v"=> R J T
local notation "u"=> C J T
local notation "vT"=> M.p.profile J
local notation "vB"=> M.p.profile T
local notation "r'"=> B.span J T
set_option quotPrecheck false
variable (hP:Circlet.Pitch M.p M.K Q C r) (hp: Pads D R Q M.K C A.delay) (hc: Decked C D R B.span B.shape A.delay) (hb:goodD M.p (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) d)(hV:Nest B V) (hC:Mallow.Arrives B.shape A.delay)
local notation "F"=> (Labels.frames G).level d
local notation "n₀"=> A.B.a.S.side m n
local notation "n₁"=> A.B.a.S.side (m+1) n
variable {K:In A.B.a m n} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
local notation "K!"=> K z.val
variable (hz:Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1))))) (h!:HasSlots (K z|>.p) (K z|>.activities))
-- wrap etc. earn with fixed Glider.
local notation "β" => (K z.val).beta
local notation "Ω"=> badge G n₁ d
local notation "w"=> B.span J T
local notation "Xp"=> (localSection G d).footprint (0:Site n₁)
local notation "Yp"=> (plate Z Ω).support
open PPX Next.Free WardBin.Lies
-- expose Leg without footing.Help alignment
variable (i:((Labels.frames G).level d).Index)
local notation "θ!"=> Cub.title G vT
local notation "T!"=> lark (K z) i hz h!
local notation "c0"=> (K z).p
local notation "U!"=> (X)
local notation "f!"=> hills (K z) i
local notation "Z0"=> icon Z Ω
local notation "q'"=> Chi.canonical
set_option quotPrecheck false
include h! hm hP hp hc hb hV hC
open Multi.Puff Source Bid
local notation "M0"=> (M.p.profile T)
local notation "v0"=> ((L).val:ℂ)^d
local notation "F0"=> (Blush.pane Z T! v0 Z0)
local notation "t0"=> ((B₁).threshold)
local notation "S!"=> localSection G d
local notation "p'"=> (WaterLevels.forecast V m N n)
local notation "f0"=> pupil H z (T!).live
local notation "f1"=> pupil H z (T!).pale
local notation "r0"=> Blush.screen Z T! f0 f1 v0 F
local notation "Scope"=> Blush.scope Z T! (0:Site n₀)
variable (g:G.Simple)
    (he : (A.B.bake.make meshT).rep N n m = H.result z.val) (ht : (A.B.bake.make meshT).rep N n (m+1) = K z.val) (choice : (A.B.bake.make meshT).Selected)(hvK: HasSlots ((A.B.bake.make meshT).rep N n m).p ((A.B.bake.make meshT).rep N n m).activities) (hd : d+3≤ A.B.a.clock.J m) {E:ℕ→ℝ}
    (h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)(hi:i≠0)
local notation "yT"=> authors A.B.a m
include he ht hd h' hY hκ hi choice hvK g hz
open YM.MergeProof
local notation "duel₀" => duet _ _ _ _ he ht (sandboxK H z)
set_option maxHeartbeats 960000 in
-- hz passed
lemma jewelJ (D':Eve J T d (M0).order L vB vT (query M.p M.K J T) M.p.kernel u v (B.target J T) (B.walls J T) (B.shape.o J T) (B.shape.μ J T) y (B.span J T)) (hs:4≤ A.B.a.clock.J m) (hj:d ≤ A.B.a.clock.J (m+1)) (hJ:Blend 2 (B₂).threshold (B₁).threshold)
    (Wg:Lotus.Wing→Prop)(hW:Wg (.logKey Ω))(hv:Heir.Release.accepts w (vT).supportExponent ((vB).supportExponent+2) L):
    let P:=Warehouse.flight (Issue.trail V) N m; let Zx:=Seal.donne S! (sound G d) M.p.kernel.penalty_pos hs (Next.Foundations.valuation G d) P hj hJ; let x:= Size.axis F i
    let p:= Extra.Histories.primary 0 x
    Matric.Span S! (A.B.bake.make meshT) N n m (hol G) (eventK H z T! (d:=d) (Guard.Keeper.sufficient hvK)) (p.exponentialEntry 0 S! (K z)) 0 0 duel₀ Wg (p.density 0 S! (K z)) (Zx.leads L x) (Doors.rate L*(F).coeffSize ((F).core x)) (E J*(F).coeffSize (vowel F L ((F).core x))) (2*(Real.exp ((K z).p.supportExponent)*Cub.title G vT)) :=by
   intro P Z' x' p; let U:= T!; let Vπ:= duel₀ -- edit
   have hh' : d ≤ A.B.a.clock.J m:=Nat.le_trans (Nat.le_add_right d 3) hd
   let G':= primaryJ hm hP hp hc hb hV hC H z hz h! i g he ht hvK hd h' hY hκ hi D' hs hj hJ hv
   have hx: p.density 0 (localSection G d) (K z)= U.milk:= (larkS (K z) i hi (h:=hz) h!).symm
   have hM : U.live.crest= Xp := skin ..
   have hr : minSide G d ≤ (K z).p.B:=by
      have hr:=hc.buys _ _ hb.1 (first_le A.B.valid m) _ (A.B.valid.pays m) d hj|>.geometry.2; rw [show (K z).p=B₂ from (H.knows _ z.2).1.point,(Circlet.shifting (A:=A) (m:=m)).2]; exact hr
   have hp'(uQ:ℝ) (h: Matric.Span S! (A.B.bake.make meshT) N n m (hol G) (eventK H z T! (d:=d) (Guard.Keeper.sufficient hvK)) (p.exponentialEntry 0 S! (K z)) 0 0 Vπ Wg (p.density 0 S! (K z)) (Z'.leads L x') (Doors.rate L*(F).coeffSize ((F).core x')) (E J*(F).coeffSize (vowel F L ((F).core x'))) uQ) (ht:uQ ≤ 2*(Real.exp ((K z).p.supportExponent)*Cub.title G vT)):
      Matric.Span S! (A.B.bake.make meshT) N n m (hol G) (eventK H z T! (d:=d) (Guard.Keeper.sufficient hvK)) (p.exponentialEntry 0 S! (K z)) 0 0 Vπ Wg (p.density 0 S! (K z)) (Z'.leads L x') (Doors.rate L*(F).coeffSize ((F).core x')) (E J*(F).coeffSize (vowel F L ((F).core x'))) (2*(Real.exp ((K z).p.supportExponent)*Cub.title G vT)):=by
       obtain ⟨hP,hT⟩:=h; exact ⟨hP, hT.climb le_rfl ht le_rfl⟩
   have hP0: Fancy S! (A.B.bake.make meshT) N n m (hol G) (p.density 0 S! (K z)) Scope r0 (Z'.leads L x') yT (Doors.rate L*(F).coeffSize ((F).core x')) (E J*(F).coeffSize (vowel F L ((F).core x'))):=hx.symm ▸ G'
   apply hp' _ (thunderJ g hm choice hC H z he ht hY hh' U (Guard.Keeper.sufficient hvK) Wg hW (hM.symm ▸ ankle) _ _ _ _ _ _ ?_ ?_ hP0) (mul_le_mul_of_nonneg_left (tallyH _ _ _ _ hr) zero_le_two)
   · let F':=hills (K z) i; let O':=masked (K z).p.threshold (Xp) F'
     have hv: p.exponentialEntry 0 S! (K z) = O':=by
       funext V; unfold p; simp only [Extra.Histories.primary,Coefficient.exponentialEntry]; unfold x'; simp_rw [Size.core_axis (F),if_neg hi,show Size.axis (F) i 0=0 from Pi.single_eq_of_ne hi.symm _,zero_add];
       change O' V+∑' j, p.maskedTerm (K z) j V= O' V -- edit
       have hh j:p.maskedTerm (K z) j V=0:= congr_fun (map_zero (Push.Local.maskLinear _ _)) V
       simp_rw [hh,tsum_zero,add_zero]
     rw [hv]; funext j; change _ = (↑(O' j).re:ℂ)+Complex.I*↑(O' j).im; rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
   funext i j; change (0:ℂ)=0+Complex.I*0; simp
end YM.PhysicalNext.Repeat.Cub
