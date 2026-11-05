import YM.RG12.Spins.Swap8
import YM.UVExtension.Forest.Glue
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
include h! hm hP hp hc hb hV hC hz
omit hC
open Multi.Puff Source Bid
open Pressure.Testing
set_option maxHeartbeats 1200000 in
theorem colorion {ε:ℝ}(G':Legato.Pads8 (M:=M) D C Q R B.span ε A.delay) (hi:((F).grades i).2=2) (a:ℂ→L[ℝ]ℝ)(h':‖a‖ ≤1) :
    let f:= a ∘ (f!); let σ:= deem 0 y (V1) f
    let κ:= fun (j:Tree.Forest (X).ratio)(k:(X).Choices)=> Mercury.hore Z Ω v Chi.canonical Chi.canonical 1 f j k
    ∀ l k:Directions G n₀,(B₁).dirBound 0 l→(B₁).dirBound 0 k →∀ j k', ‖leftDerivs (κ j k') [l,k] 1 - leftDerivs σ [l,k] 1‖ ≤ (y ^ ε)/y :=by
      intro f σ κ l k hl hk j k'
      have hv := united (n:=n) hm hP hp hV|>.2
      let a':=(K z).p
      have hq:=H.knows _ z.2
      have he:(K z).p=B₂:= hq.1.point
      let W:= B.pledging.conducts
      have hT':=(Circlet.boats (p:=n) hP.crown V hm (fun n k s h=> W.full _ _ _ h)).2 -- order k s
      have hj:= step_paid A.B.a m
      have hJ:=Rain.jersey (A:=A) (m:=m)
      have hW : Walled X ((localSection G d).footprint (0:Site n₁)) Yp y w:= mines H z h!
      have ht : ((K z).activities.reg Ω).support= Xp:=by rw [signboard (K z) h!]
      let b':=((K z).activities.reg Ω).support
      have ha (x:ℂ): ‖a x‖ ≤ ‖x‖:= (a.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) h')
      obtain ⟨hA,hB,hκ,hK,hr⟩:= inks (K z) i hz h! a ha
      have hT:= Circlet.shifting (A:=A) (m:=m)
      have hd:d ≤ J:= (Nat.le_add_right d 2).trans hb.2.2.2
      have hU:=A.B.valid.pays m
      have hL:=hc.buys _ _ (step_paid A.B.a m) (first_le A.B.valid m) _ hU d hd|>.geometry.2
      have hL': coverNumber a'.B b' ≤1:= by unfold b' a'; rw [ht,he,hT.2]; exact close_stencil G d _ _ hL _
      have hQ:((X).patch).L=L:= PriceCompiler.block_eq A.B.valid m
      rw [← he] at hv hT -- hW doesn't contain B
      have hE: Heir.Short X a' b':=lt_of_le_of_lt (Nat.pow_le_pow_left hL' _) (by have hh:= (X).patch.coarse; simpa using Nat.lt_of_lt_of_le (by decide:1<3) hh)
      have hZ:=G' J y hU _ hj (first_le A.B.valid m)
      unfold Legato.Skill at hZ
      have hs': (100*(1+radiusB y)≤ (n₀).val):=by rw [add_comm 1]; exact A.B.a.fits.sizeT ..
      have ho: (0:Site n₁) ∈ b':= by unfold b'; rw [ht]; exact ankle -- ankle function?
      have hb': betaF G y L/2 ≤ (K z).beta:= by rw [← PriceCompiler.beta_eq A.B.valid]; exact hq.2.1
      have he0: (X).ratio.parent 0=0:= ((X).ratio.root.map_zero : (X).ratio.embed 0=0) ▸ (X).ratio.embed_parent 0
      rw [← he0] at hl hk
      have hW' : Walled X ((K z).activities.reg Ω).support Yp y w:= by rw [ht]; exact hW
      rw [← ht] at hr
      have hQ0:= hZ (K z).beta hb' X (V1) hQ rfl hT' hs' (mapcase Z Ω j) (1:Config G n₁) («B»:=B₁) («B'»:=(K z).p) hJ.2.1 hv.rehearsed.tensions.coarse hT.1 hv.rehearsed.weft.cover hv ho hE hW' hL' k' Chi.canonical Chi.canonical 1 d hd i a h' hi
      have hF : Place.copy (F) i = Size.axis (F) i := rfl -- maybe needs ext
      rw [hF] at hQ0; specialize hQ0 hK hr -- may fail replace w rw
      have h:=hQ0 l k hl hk
      unfold κ Mercury.hore; rw [muse V]; apply h
end YM.PhysicalNext.Repeat.Cub
