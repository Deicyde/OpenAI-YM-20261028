import YM.FullVolume.Panel.Fares
import YM.FullVolume.Panel.GemR
import YM.FullVolume.Panel.Fleece
import YM.FullVolume.Panel.Heaven
import YM.FullVolume.Panel.BasicR
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Price
import YM.MergeProof.Basal
import YM.MergeProof.Beacon
import YM.MergeProof.Rosin
import YM.MergeProof.Volley
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris







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
   {r p:ℕ→ℕ} {R:ℕ→ℕ→Record}{B:Factor A}{V:Bolt A}
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
variable {K:In A.B.a m n} {meshT:ℕ→∀ p, Trail A.B.a p} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
set_option quotPrecheck false
open PPX MergeProof Next.Free Bid
variable (he : (A.B.bake.make meshT).rep N n m=H.result z.val) (ht: (A.B.bake.make meshT).rep N n (m+1)=K z.val) (g:G.Simple)
   (hC': Graces.Moms B.prices M.K B.span M.p.floorL)(hw: Graces.Cruise B.prices D B.recordP B.span B.shape A.delay) (hT: Cub.MainTest B.target B.expense B.span D B.shape C R A.delay)
   {E:ℕ→ℝ}(h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)
local notation "H!"=> A.B.bake.make meshT
local notation "DO"=> duet (A.B.bake.make meshT) N n m he ht (sandboxK H z)
local notation "Rt"=> K z
local notation "ε0"=> Cub.title G vT
local notation "Πt"=> localSection G d
open MergeProof.Matric
variable (choice : (A.B.bake.make meshT).Selected)(hs: HasSlots ((A.B.bake.make meshT).rep N n m).p ((A.B.bake.make meshT).rep N n m).activities)(hr : HasSlots (K z).p (K z).activities)
local notation "sk"=> Guard.Keeper.sufficient hs

abbrev prepare (T':Cloud (K z)):= closeK sk (eventK H z T' (d:=d) sk)
def border (hb: Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1))))) (i:(F).Index): Pin F n₀:= if i=0 then closeK sk (Extra.Histories.primary 0 (((L).val:ℂ)^d • (F).e0)) else prepare H z hs (lark (K z) i hb hr)
private lemma seek {G':Gauge}{n:Side}(B:BudgetPoint)(X_:Support n)(F_:Config G' n→ℂ)(h:∃ c,B.supBounds 0 X_ F_ c): B.supBounds 0 X_ F_ (sInf {y_| B.supBounds 0 X_ F_ y_}):= ⟨le_csInf h (fun i hi=> hi.1), fun i hi l hl ht=> le_csInf h (fun i' hf=> hf.2 i hi l hl ht)⟩
def cologne (i:ℕ) (f:Config G (A.B.a.S.side (m+1) n)→ℂ):Pin F n₀:=
   if h: RegFit (K z) 0 d (hol G) (mapSeat i) f ∧ ∃ c,(K z).p.supBounds 0 (mapSeat i) f c then
       prepare H z hs (float (K z) 0 (mapSeat i) (spot _ _) f _ h.1.smooth (seek _ _ f h.2) hr)
   else 0
-- sector.B empty K also at qualified.`
private lemma doze {ι:Type}[Nonempty ι](f:ι→ℂ)(h:∃ y_:ℝ,∀ V,‖f V‖≤y_)(V): ‖f V‖ ≤ sInf {y_|∀ V,‖f V‖≤y_}:= le_csInf h fun u_ hu=> hu V
def trick (i:ℕ)(f:Config G (A.B.a.S.side (m+1) n)→ℂ):Pin F n₀:= if h: SlotFit (K z) 0 i f∧ f ≠ 0 ∧ ∃ c:ℝ,∀ U,‖f U‖ ≤ c then prepare H z hs (fan (K z) 0 i f _ (doze f h.2.2) h.1) else 0
-- expose actual rows
abbrev shade (hb:Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1))))) : MergeProof.Matric.Plate F n₁ n₀:= ⟨Cub.border H z hs hr hb, cologne H z hs hr, trick H z hs⟩
variable (hsBlend: Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1)))))
local notation "tap"=> Cub.shade H z hs hr hsBlend
local notation "ζ0"=> (2*(Real.exp ((H!).rep N n (m+1)).p.supportExponent*ε0))
include g choice hs hr hP hp hc hb hV hC hC' hw hT he ht h' hY hκ hm
-- choose guard L same. t≈τv. cast valuation map.Record.v
set_option maxHeartbeats 450000 in
lemma ledgerHere (hd: d+3≤ T):
   ∃ Vj:Extra.Histories.Heading F, ∀ (Xk:Wing→Prop), (∀ (i:Support n₁)(he:0∈i), Xk (.logKey (Blush.found 0 i he))) → MergeProof.Matric.Plate.Prints Πt H! N n m (hol G) tap Vj (E J) (Doors.rate ((H!).S.block m)) (2*(Real.exp ((H!).rep N n (m+1)).p.supportExponent* Cub.title G vT)) DO Xk :=by
  -- copy Glass
  let Tx:= A.B.a; let i:= Tx.clock.J m; let j:=Tx.clock.J (m+1); let L':=D.L j; let K₀:= Tx.budget m; let K':= Tx.budget (m+1)
  let R₀:= localSection G d; let H':= (A.B.bake.make meshT); let V₀ :=H'.rep N n m; let V₁:=H'.rep N n (m+1); let a:= K'.threshold; let b:= K₀.threshold
  have hz := step_paid A.B.a m
  have hδ : d+3≤ i:=hd; have hq: d ≤ i:= (Nat.le_add_right d 3).trans hδ
  have hj:d ≤ j:= hq.trans hz.1
  obtain ⟨T'⟩:= hT _ _ (A.B.valid.pays m) i d (first_le A.B.valid m) hz hδ
  let W:= M.p.kernel; have hb' : Blend 2 a b:= T'.scaleP _ _ rfl (Circlet.shifting (A:=A) (m:=m)).1
  have hi:= Tx.clock.adm m; have hj':=Tx.clock.adm (m+1); let P':=Warehouse.flight (Issue.trail V) N m; let k:= Seal.donne R₀ (sound G d) W.penalty_pos hi (Next.Foundations.valuation G d) P' hj hb'
  let uP:= matrix R₀ (sound G d) (Carrier.stored P' W.penalty W.penalty_pos hi) a b
  let cap:= Seal.cap R₀ (sound G d) W.penalty_pos hi (Next.Foundations.valuation G d) hj' hj (one_le_two (α:=ℝ))
  have he':(H!).S.block m=L:=PriceCompiler.block_eq A.B.valid m
  let ν:=(H!).rep N n m
  refine ⟨k,fun Xk hx=>?_⟩ -- hp with arg ht. apply Volley turnout
  have hβ: (Rt).p= K' := (H.knows _ z.2).1.point
  have hE:Real.exp ((H!).rep N n (m+1)).p.supportExponent=Real.exp (Rt).p.supportExponent:=by rw [ht]
  rw [he',hE]; let ay:= E j; let u0:= Doors.rate L; let t':=2*(Real.exp (Rt).p.supportExponent*ε0)
  let W':= (A.B.bake.make meshT); let K0:= W'.rep N n (m+1)
  apply printsWave Πt H! N n m (hol G) (K z) L tap ht he'; constructor
  case heading=>
     have hσ: Planned.GuardedAtom.Forecast uP cap:= Cub.leading P' R₀ (sound G d) (Next.Foundations.valuation G d) W hi hj hb'
     have hh: Local.triangularPrice F cap ≤ E J:= (h' _ _ hz (first_le A.B.valid m) d hd).2 hj' hi hj
     intro i'; exact hσ.quote hh i'
  case main=>
    intro i' Q' p₁
    change Span Πt H! _ _ _ (hol G) (tell (Cub.border H z hs hr hsBlend i')) _ _ _ _ _ _ _ _ _ _
    unfold Cub.border; split
    next hi' =>
       subst i'; have hp : 0 ≤ t':=mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Cub.title_one ..)))
       have h:=MergeProof.currencyX Πt H! N n m (hol G) (K z) L Xk DO choice hm ht he' ay u0 t' hp k
       change Span _ _ _ _ _ _ _ _ _ (Q' 0) _ _ _ _ _ _ _;rw [show Q' 0=1 from Pi.single_eq_same _ _];
       exact Matric.Span.close sk h choice hm.le
    next hi' =>
       have hwz:Heir.Release.accepts (B.span J T) (M.p.profile j).supportExponent ((M.p.profile i).supportExponent+2) L:= hC' _ _ d hb _ (D.large _).need|>.1
       have h:= jewelJ hm hP hp hc hb hV hC H z hsBlend hr i' g he ht choice hs hd h' hY hκ hi' T' hi hj hb' Xk (hx _ ankle) hwz
       have hQ:= Matric.Span.close sk h choice hm.le
       rw [show Q' 0=0 from Pi.single_eq_of_ne (Ne.symm hi') _]; exact hQ
  case regular=>
    intro i' f x₁ t₁ t₂ hq hp'
    let t:= sInf {b| (K z).p.supBounds 0 (mapSeat i') f b}; have hg: (K z).p.supBounds 0 (mapSeat i') f t:= seek _ _ f ⟨_,hp'⟩; have ht' : t ≤ x₁:= csInf_le ⟨0,fun _ h=> h.1⟩ hp'
    have hX : (tap).tint i' f=prepare H z hs (float (K z) 0 (mapSeat i') (spot _ _) f t hq.smooth hg hr):= by unfold shade; dsimp only; unfold cologne; rw [dif_pos ⟨hq,x₁,hp'⟩ ]; rfl -- about `spot`
    have hz:= basalJ g hm hs choice hC hC' hw hd hY hκ H z ht he hr (mapSeat i') t f hq hg Xk (hx _ (spot _ _))

    have hZ: (K z).p.mass (mapSeat (n:=n₁) i') t ≤ (Rt).p.mass (mapSeat (n:=n₁) i') x₁:= mul_le_mul_of_nonneg_left ht' (Real.exp_pos _).le
    have hv' := mul_le_mul_of_nonneg_left hZ (Doors.rate_pos L).le
    rw [hX];  exact (Matric.Span.close sk hz choice hm.le).weaken hv' hv' (mul_le_mul_of_nonneg_left hZ zero_le_two)
  case forced=>
    intro i' f c' q' hh hx' hf hg he''
    let t:=sInf {b|∀ V,‖f V‖ ≤ b}; have hz'(p):‖f p‖ ≤ t:=doze _ ⟨c',he''⟩ _
    have hp': t ≤ c':=csInf_le ⟨0,fun y' hy=>le_trans (norm_nonneg (f 1)) (hy _)⟩ he''
    have hX:(tap).ink i' f=prepare H z hs (fan (K z) 0 i' f t hz' hf):= by unfold shade; dsimp only; unfold trick; rw [dif_pos ⟨hf,hh,c',he''⟩]; rfl
    let o:= (K z).p.mass ((K z).activities.forced i').support t
    have hS:0≤ Real.sqrt (A.B.a.clock.forcedAllowance (m+1)):= Real.sqrt_nonneg _
    have hV : o≤ (K z).p.mass ((K z).activities.forced i').support c':= mul_le_mul_of_nonneg_left hp' (Real.exp_pos _).le
    have hv:=mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hV hS) (Doors.rate_pos L).le
    have heK:= heavyJ g hm hs choice hC H z he ht hY hκ hq Xk i' f t hx' hh hf hz'
    rw [hX]; exact (Matric.Span.close sk heK choice hm.le).weaken hv hv (mul_le_mul_of_nonneg_left hV zero_le_two)
  intro i; change Cub.trick H z hs i 0= _; unfold trick; rw [dif_neg (fun ⟨_,r,_⟩=>r rfl)]; rfl
end YM.PhysicalNext.Repeat.Cub
