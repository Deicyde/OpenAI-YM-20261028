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
local notation "M0"=>M.p.profile T
local notation "q0"=> (K z).p
include hp hb hm hV hP hC
-- receipt for REG payload. true.
set_option maxHeartbeats 500000 in
lemma desert (I: Medal G J T d (M0).order L vB vT M.p.kernel u v (B.target J T) (B.walls J T) (B.shape.o J T) (B.shape.μ J T) y ξ₀ z' (B.span J T)) (F':Leaf (K z))(ρ : Config G n₁→ℝ)(j:ℕ) (hδ:F'.turn=.logKey j)(hω:F'.ingredient=masked (q0).threshold ((K z).activities.reg j).support ρ)(hy: (B₁).B < coverNumber (B₁).B (plate Z j).support)
    (hΩ: ((K z).activities.reg j).site=(0: Site n₁)) (h: (q0).Regular ((K z).activities.reg j).support ρ) : let U:=matin F' Z (icon Z j) Chi.canonical; let p:=(plate Z j).support
   (B₁).Regular p U∧∃ t:ℝ,(B₁).supBounds 0 p U t ∧ t ≤ sprite G y L z' * (q0).mass F'.crest F'.weight:=by
   intro U pH; have hΨ:= hC _ _ (A.B.valid.pays m) _ hb.1 |>.1
   obtain ⟨p₁,b₂,y₀,gP,v₀,Y',g₁,C',g',e,uc,hX,hQ,N'',hη⟩:= hΨ.2 _ _ _ _ (Opera.protocol A.B hm B.pledging.conducts.full) _ _ Z
   have hp': (q0)=(B₂) := (H.knows _ z.2).1.point
   have hR:= (united (n:=n) hm hP hp hV).1; rw[← hp'] at hR
   obtain ⟨hJ,hA,hτ,hF⟩:=Rain.jersey (A:=A) (m:=m)
   have he: F'.crest= ((K z).activities.reg j).support := by unfold Leaf.crest; rw[hδ];rfl
   have hv : (plate Z j).site=0 := by change (X).ratio.parent ((K z).activities.reg j).site = _; rw [hΩ,anchor0]
   have hU:= Mercury.cornice Z F' j hδ v Chi.canonical N'' hR hη hJ.le
   have hπ:= B.pledging.agenda _ _ hb.1 |>.1; rw [← hτ] at hπ
   obtain ⟨C,hN,hX⟩:= Mercury.hazy Z F' j hδ N'' hη hX hπ hΨ.1 (by rw [he]; exact mem_image.mpr ⟨(K z).activities.reg j|>.site,(K z).activities.reg j|>.anchor,rfl⟩) hJ rfl rfl hy.le
   refine ⟨hU,C,hv ▸ hN,?_⟩; have hY: C ≤ Local.reservedMass B₁ (plate Z j).support C:=le_mul_of_one_le_left hN.1 (Real.one_le_exp (by have hu:=(B₁).exponent_pos; positivity))
   rw[hA] at hX; exact ((hY.trans hX).trans (mul_le_mul_of_nonneg_right I.talent (F'.profit.trans ((q0).loMass _ _ F'.profit))))
end YM.PhysicalNext.Repeat.Quince
