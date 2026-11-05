import YM.TraceExtension.Quince.Cache
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
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
open Cub Malachite
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
local notation "w0"=> ((M.profile T).supportExponent+2)
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
local notation "v0"=> ((L).val:ℂ)^d
local notation "t0"=> ((B₁).threshold)
local notation "S!"=> localSection G d
local notation "p'"=> (WaterLevels.forecast V m N n)
open Source Bid MergeProof
local notation "PathH"=> Issue.trail V
local notation "R₀"=> (PathH).rep N n m
variable (g:G.Simple)
    (hew : (Issue.trail V).rep N n m = H.result z.val) (htw : (Issue.trail V).rep N n (m+1) = K z.val) (hd : d+3≤ A.B.a.clock.J m) {E:ℕ→ℝ}
    (h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)
local notation "yT"=> authors A.B.a m
variable {z' u' ξ₀:ℝ}
include hV hC hY hm hκ hd htw hew g
local notation "M0"=>M.p.profile T
set_option maxHeartbeats 650000 in
lemma gasT (I:Medal G J T d (M0).order L vB vT M.p.kernel u v (B.target J T) (B.walls J T) (B.shape.o J T) (B.shape.μ J T) y ξ₀ z' (B.span J T)) (s:ℕ) (O:Config G n₁→ℂ) (hs : SlotFit (K z) 0 s O)(c:ℝ)(hA:∀ t, ‖O t‖≤c):
    let d':=(K z).p.mass ((K z).activities.forced s).support c; let t:=(d'/Real.sqrt (A.B.a.clock.forcedAllowance (m+1)))
    PaidAtom S! PathH N n m (hol G) (Extra.Histories.fare (K z) s O) 0 (sprite G y L ξ₀*t) (Doors.rate L*t):=by
    intro w₁ t; have hG:= Doors.rate_pos (D.L J); let a:=Doors.rate L*w₁
    have hf:0≤w₁:= mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hA 1)); have hv:=glyphBound A.B.a (m+1); have hw:a ≤ Doors.rate L*t:=mul_le_mul_of_nonneg_left (le_div_self hf hv.1 hv.2) hG.le
    have hy(k:ℕ) : Real.sqrt (A.B.a.clock.forcedAllowance (m+1))=Blush.glyph (betaF G y L):= by
           rw [Blush.glyph_eq (A.B.a) (m+1), show A.B.a.clock.hatBeta (m+1)=betaF G y L from ?_];
           have ht:=PriceCompiler.beta_eq A.B.valid m; exact ht
    have hz:a≤ sprite G y L ξ₀*t:=by
       apply le_trans _ (mul_le_mul_of_nonneg_right I.gas (div_nonneg hf hv.1.le)); apply le_of_eq; unfold a; rw [← hy 0]; have h:=hv.1; field_simp
    by_cases he:O=0
    · let b:=fun f:Config G n₁→ℂ=> PaidAtom S! PathH N n m (hol G) f 0 (sprite G y L ξ₀*t) (Doors.rate L*t)
      let f:=Extra.Histories.fare (K z) s O
      have he:f=0:= by funext i; change (Real.exp ((K z).exponent i):ℂ)*(O i* _)=0; simp[he]
      apply (show b f=b 0 from congr_arg b he).mpr; unfold b
      have hi:0≤a:=mul_nonneg hG.le hf; refine ⟨0,fun i=>⟨?_, Extra.Histories.primary 0 0,?_,primary_format _,?_,?_⟩⟩
      · rw[sub_self]; simpa only[Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero] using (hi.trans hz)
      · simp only[Motion.patch]; split <;> simp[Extra.Histories.primary]
      · exact rem_mono (primary_rem 0 (Real.sqrt_pos.mpr (Extra.Histories.forcedPos ..))) (hi.trans hw)
      funext j; rw [primary_density,map_zero,mul_zero]; change 0= Motion.dance i (blast (Issue.trail V) N n m d (fun _=>(0:ℂ))) j; simp [Motion.dance, Extra.Histories.blast,StepData.push,Motion.scalar]

    apply atom_mono _ hz hw
    let F':= Blush.fan (K z) 0 s O c hA hs
    let aB:=houseS H z
    have hv := support_zero (X).ratio _ (show 0 ∈ F'.live.crest from hs.tagged he)
    have hx: ∃ s': aB.fragrances→ ℝ, SumBudget (fun i=>Local.reservedMass B₁ (locus F'.live aB 0 i) (s' i)) (coinFee G vB d L*w₁)∧∀ i,prince F'.live aB i→(B₁).supBounds 0 (locus F'.live aB 0 i) (pane aB F' v0 i) (s' i):=by
        refine ⟨fun i=>0,?_,fun i hi=>(never aB F'.live s rfl i hi).elim⟩; simp only [Local.reservedMass,mul_zero]; exact Local.sumBudget_zero (mul_nonneg (coin_pos ..|>.le) hf)
    let X':= Extra.Histories.fare (K z) s O; let hd':d ≤ T:=(Nat.le_add_right d 3).trans hd
    have hU : X'=F'.milk:=Blush.rose (K z) 0 s O c hA hs
    have hL : Fancy S! (Issue.trail V) N n m (hol G) X' (Blush.scope aB F' 0) (Blush.screen aB F' (pupil H z F'.live) (pupil H z F'.pale) v0 F) 0 yT a a := hU.symm ▸ sendsCard g hm hV hC H z hew htw hY hκ hd' F' hv hx le_rfl
    have hM: (PathH).Conv N n m:=(V.choice.represents N n m hm.le)
    obtain ⟨P,hQ,-⟩:=grow hL hM (hM.vac.symm ▸ (livelyCard hY hd' (n:=n)))
    obtain ⟨hf,hy,hV,x,y',hP,ht⟩:=hQ
    exact paid_center (fun s=>hM.good.labels.moves s 0) (sound G d) hf hy hP hV ht
end YM.PhysicalNext.Repeat.Quince
