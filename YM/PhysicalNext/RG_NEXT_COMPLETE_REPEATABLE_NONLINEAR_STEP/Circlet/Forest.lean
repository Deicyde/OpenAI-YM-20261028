import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Eco
import YM.Next.MAXWELL.Shots
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Circlet.Rebel

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
variable {τ:ℝ} (hz:Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) τ) (h!:HasSlots (K z|>.p) (K z|>.activities))
-- wrap etc. earn with fixed Glider.
local notation "β" => (K z.val).beta
local notation "Ω"=> badge G n₁ d
local notation "w"=> B.span J T
local notation "Xp"=> (localSection G d).footprint (0:Site n₁)
local notation "Yp"=> (plate Z Ω).support
include hm h! hp hC hc hP hV hb 
variable (i:((Labels.frames G).level d).Index)(hi:i≠0)
local notation "Mi"=> ((F).grades i).1
-- conductor boost
variable (U:Cliff G (M.p.profile (A.B.a.clock.J m)).order (M.p.profile (A.B.a.clock.J m)).power (M.p.profile (A.B.a.clock.J (m+1))).power ((((Labels.frames G).level d).grades i).1-1) (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (B.span (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (M.p.profile (A.B.a.clock.J m)).supportExponent (M.p.profile (A.B.a.clock.J (m+1))).supportExponent M.p.kernel) (a:ℂ→L[ℝ]ℝ)(h₁:∀ t,‖a t‖ ≤ ‖t‖)
local notation "leaf₀"=> cove (K z) 0 Xp ankle _ _ (lofty (K z) i hz).1 (lofty (K z) i hz).2 a h₁ h!
local notation "f'"=> a ∘ (hills (K z) i)
local notation "p"=> (K z.val).p -- conflict ℕ→ℕ
include hi
-- Graces.Moms only used for Phase.Scale q length requirement. introduce explicit.L
local notation "v0"=> ((L).val:ℂ)^d
local notation "V₀"=> (L)
local notation "ℓ"=> ((V₀).val:ℝ)
local notation "T!"=> lark (K z) i hz h!
local notation "U₁"=> (T!).live
local notation "U₂"=> (T!).pale
local notation "Y!"=> Yp
lemma pride (hv: Heir.Release.accepts (B.span J T) (vT).supportExponent ((vB).supportExponent+2) L):∃ s:(houseS H z).fragrances→ℝ, SumBudget (fun j=>Push.Local.reservedMass B₁ (locus U₁ Z 0 j) (s j)) (2*(U.charge+1)*((D.L (A.B.a.clock.J (m+1))).val:ℝ)^(d-(((Labels.frames G).level d).grades i).1)*((K z).p.mass Xp τ)) ∧ ∀ j,prince (T!).live Z j → (B₁).supBounds 0 (locus (T!).live Z 0 j) (pane Z T! v0 j) (s j):=by
   obtain ⟨t₀,h,h₁⟩:= tallyS hm hP hp hc hb hV hC H z hz h! i hi U Complex.reCLM juror hv
   obtain ⟨t₁,hK,h₂⟩:= tallyS hm hP hp hc hb hV hC H z hz h! i hi U Complex.imCLM jurorI hv
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
   · let Q:=(U.charge+1)*ℓ⁻¹^Mi*R'.mass Xp τ
     change ∑' i,q i ≤ _; rw [tsum_eq_single I he]; unfold q f; rw [if_pos rfl]; rw [show locus U₁ Z 0 I=Yp from grinchY Y U₁ Ω ha 0]; calc
       _ = ℓ^d*(Local.reservedMass B₁ Yp t₀+Local.reservedMass B₁ Yp t₁):=by unfold Local.reservedMass u₀; ring
       _ ≤ ℓ^d*(Q+Q):=by gcongr
       _ = _:=by
           unfold Q; let l:=ℓ; have hv :0<l:=by unfold l; positivity
           have hs:ℓ^d*ℓ⁻¹^Mi=ℓ^(d-Mi):=by
             nth_rw 1 [← Nat.sub_add_cancel ((Labels.frames G).level d |>.bound i)]; -- dependent hazard
             rw [pow_add,mul_assoc, ← mul_pow, mul_inv_cancel₀ hv.ne', one_pow,mul_one]
           change _ *(_*_ *R'.mass _ _+_*_ *R'.mass _ _)=_*_*R'.mass Xp τ
           rw [← hs]; ring
   have hs:j=I:= (grinch Y U'.live Ω ha).2 _ hy; subst j
   unfold f; rw [if_pos rfl,show locus U₁ Z 0 I=Yp from grinchY Y U₁ Ω ha 0]
   -- regular
   obtain ⟨hp,hL⟩:= united (n:=n) hm hP hp hV; have hO:=B.pledging.conducts; have hJ:= Rain.jersey (A:=A) (m:=m); rw [← show (K z).p = B₂ from (H.knows _ z.2).1.point] at hp; obtain ⟨p',t₃,qz,d',y₀,gP,v₀,Y',g',e,uC,hX,hY,N'',hη⟩:= hC _ _ (A.B.valid.pays m) _ hb.1|>.1.2 _ _ _ _ (Opera.protocol A.B hm hO.full) _ _ Z
   have hf:= ornate (Mercury.cornice Z U₁ Ω ha v Chi.canonical N'' hp hη hJ.1.le)
   have he:= pricingG (Mercury.cornice Z U₁ Ω ha v Chi.canonical N'' hp hη hJ.1.le) h
   have hu:= Mercury.cornice Z U₂ Ω hu (R J T) Chi.canonical N'' hp hη hJ.1.le
   have hs:= bound_add hf (regular_smul Complex.I (ornate hu)) he (bound_smul Complex.I (pricingG hu hK))
   -- output
   unfold u₀; rw [← hl]; rw [Complex.norm_I,one_mul] at hs; exact bound_smul _ hs
end YM.PhysicalNext.Repeat.Circlet
