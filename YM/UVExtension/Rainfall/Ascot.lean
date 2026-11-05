import YM.UVExtension.Rainfall.Baize
import YM.UVExtension.Rainfall.Cinders
import YM.UVExtension.Rainfall.Panes
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
   {r p:ℕ→ℕ} {R:ℕ→ℕ→Record}{B:Factor A}{V:Vintage.YM.Org.Bolt A}
local notation "cc"=> A.B.a
variable {m N n d:ℕ} (hm:m<N)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T"=> A.B.a.clock.J m
local notation "B₁"=> A.B.a.budget m
local notation "B₂"=> A.B.a.budget (m+1)
local notation "X"=> A.B.a.clock.op m n
local notation "V0"=> ships A.B N m n

local notation "L"=> D.L J
local notation "y"=> A.B.a.clock.hatBeta m
local notation "v"=> R J T
local notation "u"=> C J T
local notation "vT"=> M.p.profile J
local notation "vB"=> M.p.profile T
local notation "r'"=> B.span J T
set_option quotPrecheck false
variable (hP:Circlet.Pitch M.p M.K Q C r) (hp: Pads D R Q M.K C A.delay) (hc: Decked C D R B.span B.shape A.delay) (hb:goodD M.p (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) d)(hV:Vintage.YM.PhysicalNext.Repeat.Graces.Nest B V) (hC:Mallow.Arrives B.shape A.delay)
local notation "F"=> (Labels.frames G).level d
local notation "n₀"=> A.B.a.S.side m n
local notation "n₁"=> A.B.a.S.side (m+1) n
local notation "w0"=> ((M.profile T).supportExponent+2)
variable {K:In A.B.a m n} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
set_option quotPrecheck false
open PPX MergeProof Next.Free Bid
variable (he : (Vintage.YM.Extra.Histories.Issue.trail V).rep N n m=H.result z.val) (ht: (Vintage.YM.Extra.Histories.Issue.trail V).rep N n (m+1)=K z.val) (g:G.Simple)
   (hC': Graces.Moms B.prices M.K B.span M.p.floorL)(hw: Graces.Cruise B.prices D B.recordP B.span B.shape A.delay) (hT: Cub.MainTest B.target B.expense B.span D B.shape C R A.delay)
   {E:ℕ→ℝ}(h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)
local notation "H!"=> Vintage.YM.Extra.Histories.Issue.trail V
local notation "DO"=> duet (Vintage.YM.Extra.Histories.Issue.trail V) N n m he ht (sandboxK H z)
local notation "Rt"=> K z
local notation "ε0"=> Cub.title G vT
local notation "Πt"=> localSection G d
local notation "Rc"=> H.result z
local notation "D0"=> sandboxK H z
local notation "H0"=> Vintage.YM.Extra.Histories.Issue.trail V
local notation "κ"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "rR"=> Doors.rate L
open YM.UVExtension Eyelet UVExtension.Rainfall Lacing Lacing.RoutesF Guard MergeProof
-- underlying fixed presentation.
local notation "M0"=> A.B.a.S.side m n
local notation "g0"=> hol G
set_option quotPrecheck false
variable (hcV: Push.Local.Readable (hol G) (localSection G d) (K z|>.p) (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1))))) (hΘ:HasSlots (K z|>.p) (K z|>.activities)) (hg:Keeper (H.result z|>.p) (H.result z|>.activities))
local notation "qH"=> Keeper.sufficient hΘ
local notation "X!"=> RoutesF F n₀ n₁ (Rt).p (Rc).p (hol G)
structure Waged (M': X!) : Prop where
    route:M'.route=cart (R:=K z) (Keeper.sufficient hΘ)
    sack i: Terra H z hg hΘ i (M'.glass i)
    limb i:0 ∈ i.val.1 → Glace H z hg hΘ i (M'.wing i)
    blank i:0∉ i.val.1→ M'.wing i=0
    noneM :M'.vane none=0
    unit :M'.vane (some 0)= (((L).val:ℂ)^d • (F).e0,0)
    pace i:i≠0→ M'.vane (some i)= tars H z hg (Circlet.lark (K z) i hcV hΘ) d

variable {N': RoutesF ((Labels.frames G).level d) (A.B.a.S.side m n) (A.B.a.S.side (m+1) n) (K z|>.p) (H.result z|>.p) (hol G)} (hN: Waged H z hcV hΘ hg N') -- hcV binder.notations Lean
include g hV hκ he ht hC hC' hw hm hY
set_option maxHeartbeats 440000 in
lemma gala (hd:d+3≤ T) : ∃ M':X!, Waged H z hcV hΘ hg M':=by
    choose U hU using fun i : Eyelet.Slot n₁ => terraV g hm hV hC H z he ht hY hκ hg hd hC' hw hΘ i
    have hf(i: StockTag n₁):∃ L':Eyelet.Stream G (Rt).p i→L[ℂ] Eyelet.Bucket (F) (Rc).p (hol G) n₀, ((0∈ i.val.1 → Glace H z hg hΘ i L')∧(0∉ i.val.1→ L'=0)):=by
       by_cases h:0∈ i.val.1; swap; · exact ⟨0,fun hz=> False.elim (h hz),fun _=>rfl⟩
       obtain ⟨q,hq⟩:=glaceV g hm hV hC H z he ht hY hκ hg hd hΘ i h; exact ⟨q,fun _=>hq,fun hp=>(hp h).elim⟩
    choose v' hv' using hf
    let X'(i: (F).Index) : Eyelet.Bucket (F) (Rc).p (hol G) n₀:= if i=0 then (((L).val:ℂ)^d • (F).e0,0) else tars H z hg (Circlet.lark (K z) i hcV hΘ) d
    refine ⟨⟨fun i=> i.elim 0 X', U, v', cart (R:=K z) (Keeper.sufficient hΘ)⟩,rfl,hU, fun i j=> (hv' i).1 j,fun i hi=> (hv' i).2 hi,rfl, ?_,fun i hi=>?_⟩
    · change X' 0= _; simp [X']
    exact if_neg hi

include hN hT hP hp hc hb h'
local notation "Ψ"=> 2*(Real.exp ((K z).p.supportExponent)* Cub.title G vT)
local notation "T0"=> localSection G d
set_option maxRecDepth 6000 in
set_option maxHeartbeats 900000 in
lemma pomp (hd: d+3≤T)(hz: 0 ≤ E J): ∃ Y:Set Wing, Y.Finite∧∃ T': Heading F, Palace T0 H0 N n m (hol G) (K z) (H.result z) D0 Y qH N' L T' (E J) rR Ψ ∧ Tips N' L T' rR (E J) ∧ ∀ i:(F).Index,i≠0 → sparkT H z (Circlet.lark (K z) i hcV hΘ) d:=by
    let Tx:= A.B.a; let i:= Tx.clock.J m; let j:=Tx.clock.J (m+1); let L':=D.L j; let K₀:= Tx.budget m; let K':= Tx.budget (m+1)
    let R₀:= localSection G d; let H':= Vintage.YM.Extra.Histories.Issue.trail V; let V₀ :=H'.rep N n m; let V₁:=H'.rep N n (m+1); let a:= K'.threshold; let b:= K₀.threshold
    have hF:= step_paid A.B.a m
    have hδ : d+3≤ i:=hd; have hq: d ≤ i:= (Nat.le_add_right d 3).trans hδ
    have hj:d ≤ j:= hq.trans hF.1
    obtain ⟨T'⟩:= hT _ _ (A.B.valid.pays m) i d (first_le A.B.valid m) hF hδ
    let W':= M.p.kernel; have hb' : Blend 2 a b:= T'.scaleP _ _ rfl (Circlet.shifting (A:=A) (m:=m)).1
    have hi:= Tx.clock.adm m; have hj':=Tx.clock.adm (m+1); let P':=Warehouse.flight (Vintage.YM.Extra.Histories.Issue.trail V) N m; let k:= Seal.donne R₀ (sound G d) W'.penalty_pos hi (Next.Foundations.valuation G d) P' hj hb'
    let uP:= matrix R₀ (sound G d) (Carrier.stored P' W'.penalty W'.penalty_pos hi) a b
    let cap:= Seal.cap R₀ (sound G d) W'.penalty_pos hi (Next.Foundations.valuation G d) hj' hj (one_le_two (α:=ℝ))
    have he':(H0).S.block m=L:=PriceCompiler.block_eq A.B.valid m
    let Xk(i:Eyelet.Region n₁): Wing:= .logKey (Blush.found 0 i.val i.property); let Yq(i:StockTag n₁):Wing:= .gasKey (cart (R:=Rt) qH i); let Q':= Set.range Xk∪Set.range Yq
    have hwz:Heir.Release.accepts (B.span J T) (M.p.profile j).supportExponent ((M.p.profile i).supportExponent+2) L:= hC' _ _ d hb _ (D.large _).need|>.1
    have hℓ(i)(hi':i≠0) := starry hm hP hp hc hb hV hC H z hcV hΘ i g he ht hd h' hY hκ hi' T' hi hj hb' hg Q' (Or.inl ⟨⟨(localSection G d).footprint (0:Site n₁), ankle⟩, rfl⟩) hwz
    have hPa : Palace T0 H0 N n m (hol G) (K z) (H.result z) D0 Q' qH N' L k (E J) rR Ψ:=by
       refine ⟨⟨hg⟩, hN.route,sounds g hm H z hC, ?_,?_,?_,?_⟩
       · have hσ: Planned.GuardedAtom.Forecast uP cap:= Cub.leading P' R₀ (sound G d) (Next.Foundations.valuation G d) W' hi hj hb'
         have hh: Local.triangularPrice F cap ≤ E J:= (h' _ _ hF (first_le A.B.valid m) d hd).2 hj' hi hj
         intro i'; exact hσ.quote hh i'
       · rintro (_|l'); rw [hN.noneM]; exact dormant _ _ _ _ _ _ _ _ _ _ he ht k L
         by_cases hp:l'=0
         · subst l'; rw [hN.unit]; exact shrine _ _ _ _ _ _ _ _ _ _ he ht k _ _ _ L he' hm V.choice hg (mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (title_one ..))))
         rw [hN.pace l' hp]; change Flees _ _ _ _ _ _ _ _ _ _ _ _ (Size.axis _ l' 0) ..; rw [show Size.axis _ l' 0=0 from Pi.single_eq_of_ne (Ne.symm hp) _]; exact (hℓ l' hp).2
       · intro l' v' c' u' hp; erw [← (hN.sack l').linke v' c' hp]; exact (drifting g hm hV hC H z he ht hY hκ hg Q' hd hC' hw hΘ l' v' c' hp (Or.inl ⟨l'.1,rfl⟩)).2
       intro l' x' c' l s hc' hs
       dsimp only [l]; erw [hN.route]; by_cases h: (0:Site n₁)∈l'.val.1
       · erw [← (hN.limb l' h).linke x' c' hs]; exact (pillow g hm hV hC H z he ht hY hκ hg Q' hd hΘ l' x' c' hs h (Or.inr ⟨l',rfl⟩)).2
       have hp: x'.val=0:= not_not.mp (fun hx=>h ((wings _ _ x').posed hx))
       let N1:= cart (R:=K z) (Keeper.sufficient hΘ) l'
       erw [hN.blank l' h, hp, show exactGas (K z|>.activities) N1 0=0 from ?_,show Extra.Histories.fare (K z) N1 0=0 from ?_]
       · have hv:0≤ s :=mul_nonneg (Real.exp_pos _).le hc'; exact breeze _ _ _ _ _ _ _ _ _ _ he ht (mul_nonneg (Doors.rate_pos _).le (div_nonneg hv (Real.sqrt_nonneg _))) (mul_nonneg zero_le_two hv)
       · funext i; simp [Extra.Histories.fare]
       simp [exactGas]
    refine ⟨Q',(Set.finite_range _).union (Set.finite_range _), k,hPa,⟨⟨(Doors.rate_pos _).le,fun i j=> ?_,fun i j=>?_⟩,hz,hN.noneM,fun i=>?_⟩,fun i h=> (hℓ i h).1⟩
    · have hx:=(hN.sack i).funds j; refine ⟨?_,hx.rain,hx.stem⟩; simpa only [sub_zero] using hx.earns
    · by_cases ht : (0:Site n₁)∈i.val.1
      · have hx:= (hN.limb i ht).funds j; refine ⟨?_,hx.rain,hx.stem⟩; simpa only [sub_zero] using hx.earns
      rw [hN.blank i ht]; have hz :0 ≤ rR *‖j‖:=mul_nonneg (Doors.rate_pos _).le (norm_nonneg _); simp [Labels.Frame.coeffSize]; exact hz
    have hu := UVExtension.Rainfall.alarm _ _ _ _ _ _ _ _ he.symm hg (hPa.pivot (.some i)); exact ⟨hu.earns,hu.rain,hu.stem⟩
end YM.PhysicalNext.Repeat.Cub
