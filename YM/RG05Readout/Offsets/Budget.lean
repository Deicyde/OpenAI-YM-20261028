import YM.UVExtension.Flake.Lamps
import YM.RG05Readout.Offsets.PerCell
/-!
# Emit the raw regular + forced estimate

Adapt `Circlet.pride`→`budgetLoop` to off-center roots and supports,
`attestLoop` handles the compulsory non-principal receipts and flag terms.
No preparation of analytic packets/E2.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury Graces
open Bid Planned.PrimaryIntegral295 WaterLevels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{M : Metals G}{D:Rolls M.p}{A:Alloy M D}{Q:ℕ→ℕ→ Teller G}{C: Programs M.p}
   {r p:ℕ→ℕ} {R:ℕ→ℕ→Record}{B:Factor A}{V:Vintage.YM.Org.Bolt A} {jV : ℕ → ∀ p m,RG.Rep G (A.B.a.S.side m p)}
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
local notation "K!"=> K z.val
variable (hz:Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Next.Foundations.price G (max (M.p.profile (A.B.a.clock.J (m+1))).order (M.p.profile (A.B.a.clock.J (m+1))).power))) (h!:HasSlots (K z|>.p) (K z|>.activities))
-- wrap etc. earn with fixed Glider.
local notation "β" => (K z.val).beta
open RG05Cell
variable (b₀:Site (A.B.a.S.side (m+1) n))(hy₀: (A.B.a.clock.op m n).ratio.parent b₀=0)
local notation "Ω"=> RG05Cell.tab G b₀ d
local notation "w"=> B.span J T
local notation "Xp"=> (localSection G d).footprint b₀
local notation "Yp"=> (plate Z Ω).support
include hm h! hp hC hc hP hV hb 
variable (i:((Labels.frames G).level d).Index)(hi:i≠0)
local notation "Mi"=> ((F).grades i).1
-- conductor boost
-- Graces.Moms only used for Phase.Scale q length requirement. introduce explicit.L
local notation "v0"=> ((L).val:ℂ)^d
local notation "V₀"=> (L)
local notation "ℓ"=> ((V₀).val:ℝ)
local notation "T!"=> wood (K z) b₀ i hz h!
local notation "U₁"=> (T!).live
local notation "U₂"=> (T!).pale
local notation "Y!"=> Yp

include hi hy₀
set_option maxHeartbeats 500000 in
lemma RG05_pride (U:Cliff G (M.p.profile (A.B.a.clock.J m)).order (M.p.profile (A.B.a.clock.J m)).power (M.p.profile (A.B.a.clock.J (m+1))).power ((((Labels.frames G).level d).grades i).1-1) (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (B.span (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (M.p.profile (A.B.a.clock.J m)).supportExponent (M.p.profile (A.B.a.clock.J (m+1))).supportExponent M.p.kernel)  (hv: Heir.Release.accepts (B.span J T) (vT).supportExponent ((vB).supportExponent+2) L):∃ s:(houseS H z).fragrances→ℝ, SumBudget (fun j=>Push.Local.reservedMass B₁ (locus U₁ Z 0 j) (s j)) (2*(U.charge+1)*((D.L (A.B.a.clock.J (m+1))).val:ℝ)^(d-(((Labels.frames G).level d).grades i).1)*((K z).p.mass Xp (Next.Foundations.price G (max (vT).order (vT).power)))) ∧ ∀ j,prince (T!).live Z j → (B₁).supBounds 0 (locus (T!).live Z 0 j) (pane Z T! v0 j) (s j):=by
   obtain ⟨t₀,h,h₁⟩:= RG05_perCell hm hP hp hc hb hV hC H z hz h! b₀ i hi U Complex.reCLM juror hv
   obtain ⟨t₁,hK,h₂⟩:= RG05_perCell hm hP hp hc hb hV hC H z hz h! b₀ i hi U Complex.imCLM jurorI hv
   let I:= icon Z Ω; let Y:= (houseS H z)
   let R':=(K z.val).p; let U':= (T!)
   have ha:U'.live.turn=.logKey Ω:=rfl; have hu:U'.pale.turn=.logKey Ω:=rfl
   let u₀:=ℓ ^ d*(t₀+t₁)
   have hl:‖v0‖=ℓ ^ d:=by simp
   let f(j:Y.fragrances):=if j=I then u₀ else 0
   let q(j:Y.fragrances):= Push.Local.reservedMass B₁ (locus U₁ Z 0 j) (f j)
   have hO:0≤ u₀:=mul_nonneg (hl ▸ norm_nonneg _) (add_nonneg h.1 hK.1)
   have he j (H:j≠ I):q j=0:=by unfold q f; rw [if_neg H,Local.reservedMass,mul_zero]
   refine ⟨f,⟨fun j=> ?_,summable_of_ne_finset_zero (s:={I}) (fun i hi=> he i (by simpa using hi)),?_⟩,fun j hy=>?_⟩
   · apply mul_nonneg (Real.exp_pos _).le _; unfold f; split; exact hO; exact le_rfl
   · let Q:=(U.charge+1)*ℓ⁻¹^Mi*R'.mass Xp (Next.Foundations.price G (max (vT).order (vT).power))
     change ∑' i,q i ≤ _; rw [tsum_eq_single I he]; unfold q f; rw [if_pos rfl]; rw [show locus U₁ Z 0 I=Yp from grinchY Y U₁ Ω ha 0]; calc
       _ = ℓ^d*(Local.reservedMass B₁ Yp t₀+Local.reservedMass B₁ Yp t₁):=by unfold Local.reservedMass u₀; ring
       _ ≤ ℓ^d*(Q+Q):=by gcongr
       _ = _:=by
           unfold Q; let l:=ℓ; have hv :0<l:=by unfold l; positivity
           have hs:ℓ^d*ℓ⁻¹^Mi=ℓ^(d-Mi):=by
             nth_rw 1 [← Nat.sub_add_cancel ((Labels.frames G).level d |>.bound i)]; -- dependent hazard
             rw [pow_add,mul_assoc, ← mul_pow, mul_inv_cancel₀ hv.ne', one_pow,mul_one]
           change _ *(_*_ *R'.mass _ _+_*_ *R'.mass _ _)=_*_*R'.mass Xp (Next.Foundations.price G (max (vT).order (vT).power))
           rw [← hs]; ring
   have hs:j=I:= (grinch Y U'.live Ω ha).2 _ hy; subst j
   unfold f; rw [if_pos rfl,show locus U₁ Z 0 I=Yp from grinchY Y U₁ Ω ha 0]
   -- regular
   obtain ⟨hp,hL⟩:= Vintage.YM.PhysicalNext.Repeat.Circlet.united (n:=n) hm hP hp hV; have hO:=B.pledging.conducts; have hJ:= Rain.jersey (A:=A) (m:=m); rw [← show (K z).p = B₂ from (H.knows _ z.2).1.point] at hp; obtain ⟨p',t₃,qz,d',y₀,gP,v₀,Y',g',e,uC,hX,hY,N'',hη⟩:= hC _ _ (A.B.valid.pays m) _ hb.1|>.1.2 _ _ _ _ (Opera.protocol A.B hm hO.full) _ _ Z
   have hf:= ornate (Mercury.cornice Z U₁ Ω ha v Chi.canonical N'' hp hη hJ.1.le)
   have he:= pricingG (Mercury.cornice Z U₁ Ω ha v Chi.canonical N'' hp hη hJ.1.le) h
   have hu:= Mercury.cornice Z U₂ Ω hu (R J T) Chi.canonical N'' hp hη hJ.1.le
   have hs:= bound_add hf (regular_smul Complex.I (ornate hu)) he (bound_smul Complex.I (pricingG hu hK))
   rw [hy₀] at hs -- after coordinate sup estimates
   unfold u₀; rw [← hl]; rw [Complex.norm_I,one_mul] at hs; exact bound_smul _ hs
variable (g:G.Simple)
    (he : (History.mk A.B.a jV).rep N n m = H.result z.val) (ht : (History.mk A.B.a jV).rep N n (m+1) = K z.val) (hd : d+3≤ A.B.a.clock.J m) {E:ℕ→ℝ}
    (h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)
local notation "S!"=> localSection G d
local notation "yT"=> authors A.B.a m
local notation "Z₁" => pupil H z (T!).live
local notation "Z₂" => pupil H z (T!).pale
local notation "f!"=> Blush.screen Z T! Z₁ Z₂ v0 F
local notation "Xo" => Blush.scope Z T! 0
local notation "p"=> (K z).p
local notation "d₁"=> Doors.rate L

-- hold until PredSlot.Certificate.
include h' hY hκ he ht g hi hd
include hy₀
lemma RG05_budgetLoop (Tq : Guard.Keeper ((History.mk A.B.a jV).rep N n m).p ((History.mk A.B.a jV).rep N n m).activities) (hv: Heir.Release.accepts (B.span J T) (vT).supportExponent ((vB).supportExponent+2) L): let R₁:= (History.mk A.B.a jV).rep N n m; let κ:= (A.B.a.clock.forcedAllowance m); let x:= Size.axis F i;
    ∃ a b c :ℝ, Arrival S! (History.mk A.B.a jV) N n m (T!).milk (Xo) (f!) ∧ Nonempty (Guard.Berths R₁.p R₁.activities (fun q=> Local.joint S! 0 (Xo q))) ∧ Tare (f!) 0 (Xo) (hol G) S! R₁ yT κ (Real.sqrt κ) a b c ∧
      (∃ u' v':ℝ, YM.Planned.GuardedAtom.Deck f! 0 (Xo) R₁ (Real.sqrt κ) u' v' ∧ Push.Local.factor (hol G) S! R₁.p.supportExponent yT *u'=a) ∧ Local.turnCost R₁.p.order R₁.p.power*a+(b+c) ≤ E J*(F).coeffSize (vowel F L ((F).core x)):=by
  intro R₁ θ x0; have hs:= A.B.valid; obtain ⟨U,hU⟩:= (h' J T (step_paid A.B.a m) (first_le A.B.valid m) d hd).1 _ hi
  have ha:= RG05_pride hm hP hp hc hb hV hC H z hz h! b₀ hy₀ i hi U hv
  have hf:(0:Site n₀)∈ (U₁).crest.image (X).ratio.parent:=Finset.mem_image.mpr ⟨b₀,(by rw [RG05Cell.place]; exact toe _),hy₀⟩
  have hm':d ≤ T := Nat.le_trans (Nat.le_add_right d 3) hd
  obtain ⟨hb₁,hb₂,hT',hCard,hL,hq⟩:=attestLoop g hm hC H z he ht hY hκ hm' T! hf Tq ha
  refine ⟨_,_,_,hb₁,hb₂,hT',hCard,?_⟩; let b:= vB; let b':= vT; let wS:= b.supportExponent
  let R':= K z; let c:= credibility G b'.supportExponent b'.order b'.power; let M0:= R'.p.mass (U₁).crest (U₁).weight
  have hzeta := hc.buys _ _ hb.1 (first_le hs m) _ (hs.pays m) d (hm'.trans hb.1.1)
  have hr:R'.p=B₂:=(H.knows _ z.2).1.point
  have hr' : minSide G d ≤ R'.p.B:=by rw [hr,(shifting (m:=m) (A:=A)).2]; exact hzeta.geometry.2
  have hh : M0 ≤ c:=by
    unfold c credibility; rw [← show R'.p.supportExponent=b'.supportExponent from (by rw [hr]; exact Rain.jersey (A:=A) (m:=m+1)|>.2.2.1)]; exact RG05Cell.tally (K z) b₀ i hz h! hr'
  have hM:M0≥0:= (U₁).profit.trans (R'.p.loMass _ _ (U₁).profit)
  have hc :0≤c:= hM.trans hh
  have hV :=mul_le_of_le_one_left hM (coinFlat G (M.p.profile (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) d)
  let z1:=ℓ^(d-Mi); have hv:1≤ z1:=one_le_pow₀ (Nat.one_le_cast.mpr (L).property)
  have hx : (F).coeffSize (vowel F L ((F).core x0))= z1:=by rw [Size.core_axis,if_neg hi]; rw [show vowel F L x0= ((L).val:ℂ)^(d-Mi) • Size.axis F i from PPX.vowel_col _ i]; simp only [Size.smul,Complex.norm_pow,Complex.norm_natCast,Size.size_axis,mul_one]; rfl
  rw [hx]
  let Z' := (2*(U.charge+1)*z1*M0)
  let ξ := usage G b.order b.power d wS; have hS:0≤ ξ:=by unfold ξ usage Local.factor; exact mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Local.atomPrice_ge_one _ _ (zero_le_one.trans (Next.Foundations.price_one_le _ _))))
  let s:= Local.turnCost b.order b.power; have ht:0<s:= turnFee_pos (Time.probe b)
  have he:R₁.p.order=b.order∧ R₁.p.power=b.power:=by rw [show R₁=H.result z from he]; have h:=(Rain.jersey (A:=A) (m:=m)); exact ⟨h.1,h.2.1⟩
  rw [he.1,he.2]
  let e:= ξ*(c*z1*(1+2*(U.charge+1))); have h: M0 ≤ c*z1:=hh.trans (le_mul_of_one_le_right hc hv)
  have hμ:= U.large
  let p₀:= R₁.p
  have hp {a mQ:ℝ}(hb:a = ξ*(mQ+Z'))(hf:mQ≤coinFee G b d L * M0): a ≤ e:=by
     rw [hb]; apply mul_le_mul_of_nonneg_left _ hS
     have hh := le_trans (a:=mQ) hf (hV.trans h)
     calc
       _ ≤ c*z1+(2*(U.charge+1)*z1*M0):=add_le_add hh le_rfl
       _ ≤ c*z1+(2*(U.charge+1)*z1*c):=by gcongr
       _ = _:=by ring
  have hf: Z'=2*(U.charge+1)*z1* (K z).p.mass Xp (Next.Foundations.price G (max b'.order b'.power)):=by unfold Z' M0; rw [show (U₁).crest=Xp from RG05Cell.place (K z) b₀ i hz h!]; rfl
  change s* _ +(_+_ ) ≤ _
  refine le_trans (add_le_add (mul_le_mul_of_nonneg_left (hp (mQ:=_) (?_ ) hL) ht.le) (add_le_add (hq.trans (hV.trans h)) (hp (mQ:=_) (?_ ) hL))) ?_
  · exact congr_arg (fun a=> ξ*( (_:ℝ)+a)) hf.symm
  · exact congr_arg (fun a=> ξ*( (_:ℝ)+a)) hf.symm
  apply le_trans _ (mul_le_mul_of_nonneg_right hU (show 0≤ z1 from zero_le_one.trans hv)); unfold billG; apply le_of_eq
  change s*e+(c*z1+e)=c*(1+ξ*_*(s+1))*z1; unfold e; ring
end YM.PhysicalNext.Repeat.Circlet
