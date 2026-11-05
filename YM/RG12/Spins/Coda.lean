import YM.RG12.Spins.Clock5
import YM.RG12.Spins.WildPad
import YM.RG12.Spins.Shift
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
local notation "w0"=> ((M.profile T).supportExponent+2) -- wrong
variable {K:In A.B.a m n} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
local notation "K!"=> K z.val
variable (hz:Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1))))) (h!:HasSlots (K z|>.p) (K z|>.activities))
-- wrap etc. earn with fixed Glider.
local notation "β" => (K z.val).beta
local notation "Ω"=> badge G n₁ d
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
-- removed
open Multi.Puff Source Bid
include hm hP hp hc hb hV h! hz
local notation "D!"=> Mercury.groves
local notation "S!"=> localSection G d
local notation "φ!" η=> Mercury.hore Z Ω v Chi.canonical Chi.canonical 1 (η ∘ f!)
local notation "g!" η => fun (W:Config G n₀)=> Mercury.groves Z Ω v Chi.canonical Chi.canonical 1 W (η ∘ f!)
open YM.RG12
set_option quotPrecheck false
local notation "f₀" => ocean (V1) (f!) y
local notation "v0"=> ((L).val:ℂ)^d
local notation "F0"=> (Blush.pane Z T! v0 Z0)
local notation "C?" η:max γ:max=>cove (K z) 0 Xp ankle _ _ (lofty (K z) i hz).1 (lofty (K z) i hz).2 η γ h!
protected def cistern (d:ℕ):ℝ:= ∑ p∈ Local.tests ((Labels.frames G).level d), Cub.Ai d p.1
-- Coda exact θ.Pay on four-row of primitive pane. missing Mercado.Port.Dyadic L log cap. no claiming.E optimization choose W. include starlight.(pathsE alternative)
local notation "χℓ"=> ((A.B.a.budget m).threshold)
include hC
set_option maxHeartbeats 720000 in
lemma coda8 {ε W:ℝ} (hW:0≤W)(G':Legato.Pads8 (M:=M) D C Q R B.span ε A.delay)(hw:Legato.raft D 2 A.delay)(hS:G.Simple) (hi: ((F).grades i).2=2)
    (hF:∀ (η:ℂ→L[ℝ]ℝ)(γ:∀ x:ℂ,‖η x‖ ≤ ‖x‖),‖η‖≤ 1 → ∀ Z':Directions G n₀,(B₁).dirBound 0 Z' →
      ‖leftDerivs (Charity.matin (C? η γ) Z (icon Z Ω) Chi.canonical) [Z',Z'] 1-leftDerivs (g! η) [Z',Z'] 1‖ ≤ W)
    (hd:d+3≤ T)(hS':d≤J)(hT: Blend 2 (B₂).threshold (B₁).threshold)(hJ:4≤ A.B.a.clock.J m)(hD : Push.Local.Readable (hol G) S! B₁ n₀ (authors A.B.a m)) :
    let Z':=W+(y^ε)/y; let c:= Cub.cistern (G:=G) d*((L).val:ℝ)^d*(Z'+Z') + (y^2)⁻¹
    let P :=Warehouse.flight (Issue.trail V) N m; let hf:= PPX.Seal.donne S! (sound G d) M.p.kernel.penalty_pos hJ (Next.Foundations.valuation G d) P hS' hT
    let k := Local.weighted (hol G) (F) 0 Yp χℓ (F0)-hf.leads L (Place.copy F i)
    (F).coeffSize (Spins.four (F) k) ≤ Local.testPrice F*c:=by
     intro W' A' J' K' k
     have he:= zero_lt_one.trans (A.B.a.fits.delayed m)
     have hv':0 ≤ Cub.cistern (G:=G) d:= Finset.sum_nonneg (fun p _=>Cub.ai_pos ..)
     apply Spins.charged (F) (Local.tests (F)) (Local.testPrice F) ((Local.probe_budget (F)).choose_spec.choose_spec.2) k (by unfold A' W'; positivity)
     rintro ⟨a,l⟩ hτ ht
     have hx:=A.B.valid.pays m
     let e:=(K z).p.threshold
     have hk:(K z).p=B₂:= (H.knows _ z.2).1.point
     have hv:= (united (n:=n) hm hP hp hV); rw [← hk] at hv
     obtain ⟨aF,b,y₀,g,vα,Y',p₁,B',g',η,ν,hX,hY,N'',hη⟩:= (hC _ _ hx _ hb.1).1.2 _ _ _ _ (Opera.protocol A.B hm B.pledging.conducts.full (n:=n)) _ _ Z
     have hn:=Rain.jersey (A:=A) (m:=m)|>.1
     have h₁:= Blush.ornate (Mercury.cornice Z (T!).live Ω rfl v Chi.canonical N'' hv.1 hη hn.le); have h₂:=Blush.ornate (Mercury.cornice Z (T!).pale Ω rfl v Chi.canonical N'' hv.1 hη hn.le)
     have hF': (B₁).Regular Yp (F0):= regular_smul (v0) (regular_add h₁ (regular_smul Complex.I h₂))
     unfold k; rw [map_sub,← Local.sample_eq F _ _ _ (show (B₁).Regular Yp (F0) from hF') hD.order]
     let O:Config G n₀→ℂ:= f₀; let q'':= Local.sample (hol G) (0:Site n₀) Yp χℓ (v0 • O) (a,l)
     have hf :=quartz8 hm hP hp hc hb hV hC H z hz h! i hW G' hS hi hF a l ht
     refine (norm_sub_le_norm_sub_add_norm_sub _ q'' _).trans (add_le_add (hf.trans ?_) ?_)
     · unfold W'; have hu:Cub.Ai d a ≤ Cub.cistern (G:=G) d:= single_le_sum (fun p _=> Cub.ai_pos d p.1) hτ
       have ht':0 ≤ W+y^ε/y:= by positivity
       gcongr
     -- starlight. grocery. smooth O from basis chart
     let V':= WaterLevels.forecast V m N n; let t':=χℓ; let tlog:= testLog (hol G) d (0:Site n₀) (t' • a); let h':= (hol G).testLinks d (0:Site n₀) (t' • a)
     have hr : Germ d O (1:Config G n₀):= by
        let W(γ:ℂ→L[ℝ]ℝ):= Complex.ofRealCLM ∘ deem 0 y V' (γ ∘ f!)
        have hf (γ:ℂ→L[ℝ]ℝ):Germ d (W γ) (1:Config G n₀):=by
           have hx:= deem_focus (o:=(0:Site n₁)) hv.2 (Graces.readings γ (lofty (K z) i hz).1)
           have ho:d ≤ (vB).order:= (Nat.le_add_right d 1).trans hb.2.1
           apply Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=deem 0 y V' (γ ∘ f!) ∘ increment (1:Config G n₀)) 0 (hx.germ.of_le (Nat.cast_le.mpr ho))
        have ht : O=W Complex.reCLM + Complex.I • W Complex.imCLM:=by funext W; change _= ↑(O W).re + Complex.I*↑(O W).im; rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
        rw [ht]; exact (show Local.Chart d (W Complex.reCLM) _ from hf _).add ((show Local.Chart d (W Complex.imCLM) _ from hf _).const_smul Complex.I)
     have hK:ContDiffAt ℝ (↑l.val) (O ∘ h') 0:=by
        have hc':ContDiffAt ℝ (↑l.val) ((O ∘ increment (1:Config G n₀)) ∘ tlog) 0:= ((testLog_zero ..).symm ▸ (show Local.Chart d O (1:Config G n₀) from hr).of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ l.isLt))).comp _ ((testLog_diff ..).of_le le_top)
        exact hc'.congr_of_eventuallyEq ((increment_testLog (hol G) d 0 (t' • a)).fun_comp O)
     have hN: Nonwrapping Yp 0:= (shells hm hP hp hc hb hV H z h!).1
     have hy: q''=((L).val:ℝ)^d • iteratedDeriv l.val (O ∘ h') 0:=by
        unfold q'' Local.sample; rw [if_pos hN,show ((v0 • O) ∘ _)= (((L).val:ℝ)^d) • (O ∘ h') from (by funext x; simp only [Pi.smul_apply,Function.comp_apply,Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_natCast]; rfl), iteratedDeriv_const_smul hK]
     have hV' := hw J y hx _ (step_paid A.B.a m) (first_le A.B.valid m) d hd (a,l) hτ i n₀ n₁ X V' J' rfl (PriceCompiler.block_eq A.B.valid m) (show HEq V'.R.A0 (Carrier.linesOf J' M.p.kernel.penalty) from ?_) _ _ hT ?_ hJ hS' M.p.kernel.penalty_pos
     swap; · change HEq (Carrier.linesOf J' A.B.a.clock.kernel.penalty) _; rw [A.B.valid.kernel]
     swap; · have h:100*(radiusB y+1) ≤ (n₀).val:=A.B.a.fits.sizeT m n; unfold Heir.reach; omega
     rw [hy]; change ‖((L).val:ℝ)^d • iteratedDeriv l.val ((ocean V' (Local.presented S! (0:Site n₁) ((K z).p.threshold) (Place.copy F i)) y) ∘ h') 0 - _‖ ≤ (y^2)⁻¹; rw [hk]; exact hV'
end YM.PhysicalNext.Repeat.Cub
