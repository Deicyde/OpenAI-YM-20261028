import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Circlet.Rebel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Central
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Chant

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
lemma translate (E: Eve J T d (vB).order L vB vT (query M.p M.K J T) M.p.kernel u v (B.target J T) (B.walls J T) (B.shape.o J T) (B.shape.μ J T) y (B.span J T))
    (a':ℂ→L[ℝ]ℝ)(ha:∀ t,‖a' t‖≤‖t‖):let f:= a' ∘ (f!); let M':= deem (0:Site n₁) y (WaterLevels.forecast V m N n) f
    let s:= cove (K z) 0 Xp ankle _ _ (lofty (K z) i hz).1 (lofty (K z) i hz).2 a' ha h!
    Germ d (Charity.matin s Z (icon Z Ω) Chi.canonical) 1 ∧ Germ d M' 1∧ ∀ l:List (Directions G n₀), l.length ≤ d→ (∀ A∈l,(B₁).dirBound 0 A)→ ‖leftDerivs (Charity.matin s Z (icon Z Ω) Chi.canonical) l 1-leftDerivs M' l 1‖ ≤ (θ!)*E.sail+E.small :=by
   intro f X' M'
   obtain ⟨hM,h',hη,hs,hA'⟩:= inks (K z) i hz h! a' ha
   let K₀:=A.B.a; have h₁ : (A.B.a.params m)=vB:=params_eq A.B.valid m; have h₂: (A.B.a.params (m+1))=vT:=params_eq A.B.valid (m+1)
   have hq:= H.knows _ z.2; have he:c0=B₂:=hq.1.point
   have hZ := B.pledging.conducts; have hU := A.B.valid.pays m
   obtain ⟨b₀,b,y₀,g,v₀,Y',p',B',g',e,ν,hX,hY,N'',hρ⟩:= (hC _ _ hU _ hb.1).1.2 _ _ _ _ (Opera.protocol A.B hm hZ.full (n:=n)) _ _ Z
   have hz:=hb.1; obtain ⟨hp,hR⟩:= united (n:=n) hm hP hp hV
   have hj:= Rain.jersey (A:=A) (m:=m); have hJ:= Rain.jersey (A:=A) (m:=m+1); have hP':(c0).B= (B₂).B:= by rw [he]
   rw [← he] at hp hR
   have hD:= (Nat.le_add_right d 2).trans hb.2.2.2
   have hL :=hc.buys _ _ hz (first_le A.B.valid m) _ hU _ hD|>.geometry
   have hC':= Circlet.shifting (A:=A) (m:=m) -- conflict fixing
   have ht : ((K z).activities.reg Ω).support= Xp:=by rw [signboard (K z) h!]
   have ho: ((K z).activities.reg Ω).site=0:=by rw [signboard (K z) h!]
   have h2: coverNumber (c0).B Xp ≤ 1:= close_stencil G d (c0).B n₁ (by rw [hP',hC'.2]; exact hL.2) _
   have hy:Heir.Short X c0 ((K z).activities.reg Ω).support:=by unfold Heir.Short; rw [ht]; exact lt_of_le_of_lt (Nat.pow_le_pow_left h2 _) (by have hh:3≤ (X).patch.L.val:=(X).patch.coarse; simpa using Nat.lt_of_lt_of_le (by decide:1<3) hh)
   let t':=(A.B.a.S.side m n); let o₀:= ((K z).activities.reg Ω).site
   have hf: (c0).supBounds o₀ ((K z).activities.reg Ω).support f θ!:=by rw [ht]; unfold o₀; rw [ho]; exact hA'
   obtain ⟨hT,hK⟩:= E.cap B₁ c0 n₀ n₁ ((K z).activities.reg Ω).support rfl (he.symm ▸ hC'.1) (hP'.trans hC'.2) hj.2.1 (ht.symm ▸ h2) (K z).beta ((by rw [← PriceCompiler.beta_eq A.B.valid]; exact hq.2.1))
   have hJ:= deem_focus (o:= (0:Site n₁)) hR hs
   let V':= WaterLevels.forecast V m N n; have hV₀:Healthy (B₁).threshold Yp (1:Config G n₀):= one_healthy _ _ (B₁).threshold_pos.le
   have hn:d ≤ (vB).order:= (Nat.le_add_right d 1).trans hb.2.1
   have hh:= shells hm hP ‹Pads D R Q M.K C A.delay› hc hb hV H z h!
   have he :∀ Fx k, Mercury.hore Z Ω v q' q' 1 f Fx k= (mapcase Z Ω Fx).hymn V' (gStep (K z).beta) q' 1 k f (Baffle.magic v c0 (K z).beta q') 1:= fun Fx k=>muse V _ _ _ _ _ _ _ _
   have hu := cornice Z M' Ω hM v q' N'' hp hρ hj.1.le
   have hs' : Germ (vB).order (matin M' Z Z0 Chi.canonical) (1:Config G n₀):=hj.1 ▸ hu.smooth _ hV₀
   refine ⟨hs'.prod hn, hJ.germ.of_le (Nat.cast_le.mpr hn),fun l hl hv=>?_⟩
   have hW:= anthem Z M' Ω hM v q' q' 1 N'' hρ f hs hη hp (hj.2.1.symm ▸ E.sails) rfl hj.1.le (B.pledging.agenda _ _ hz|>.2.2) hh.2 hf hy hR he hT hb.2.1 l hl ((by rw [zeroO H z h!]; exact hv)) -- check
   rw [ho] at hW
   exact hW.trans (add_le_add_right hK _)
end YM.PhysicalNext.Repeat.Cub
