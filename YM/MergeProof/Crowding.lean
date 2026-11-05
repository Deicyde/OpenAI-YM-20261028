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
local notation "w0"=> ((M.profile T).supportExponent+2) -- wrong
variable {K:In A.B.a m n} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
set_option quotPrecheck false
open PPX MergeProof Next.Free Bid
variable (he : (Issue.trail V).rep N n m=H.result z.val) (ht: (Issue.trail V).rep N n (m+1)=K z.val) (g:G.Simple)
   (hC': Graces.Moms B.prices M.K B.span M.p.floorL)(hw: Graces.Cruise B.prices D B.recordP B.span B.shape A.delay) (hT: Cub.MainTest B.target B.expense B.span D B.shape C R A.delay)
   {E:ℕ→ℝ}(h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)
local notation "H!"=> Issue.trail V
local notation "DO"=> duet (Issue.trail V) N n m he ht (sandboxK H z)
local notation "Rt"=> K z
local notation "ε0"=> Cub.title G vT
local notation "Πt"=> localSection G d
include g hP hp hc hb hV hC hC' hw hT he ht h' hY hκ hm
-- choose guard L same. t≈τv. cast valuation map.Record.v
lemma clocksHere (hd: d+3≤ T):
   ∃ Vj:Extra.Histories.Heading F, ∀ (Xk:Wing→Prop), (∀ (i:Support n₁)(he:0∈i), Xk (.logKey (Blush.found 0 i he))) → MergeProof.Stampede Πt H! N n m (hol G) DO (E J) (Doors.rate ((H!).S.block m)) (2*(Real.exp ((H!).rep N n (m+1)).p.supportExponent* Cub.title G vT)) Vj Xk :=by
  -- copy Glass
  let Tx:= A.B.a; let i:= Tx.clock.J m; let j:=Tx.clock.J (m+1); let L':=D.L j; let K₀:= Tx.budget m; let K':= Tx.budget (m+1)
  let R₀:= localSection G d; let H':= (Issue.trail V); let V₀ :=H'.rep N n m; let V₁:=H'.rep N n (m+1); let a:= K'.threshold; let b:= K₀.threshold
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
  have hz₀: Local.Readable (hol G) (localSection G d) (Rt).p (A.B.a.S.side (m+1) n) (title G (M.p.profile j)) := hβ.symm ▸ (by
       rw [show title G (M.p.profile j) = authors Tx (m+1) from ?_]; exact lively hY hj (n:=n)
       unfold title authors; rw [show Tx=A.B.a from rfl, params_eq A.B.valid (m+1)])
  have hΨ: Progress.DirectedRecipe.HasSlots (Rt).p (Rt).activities:= ht ▸ hV.samples g N (m+1) n hm
  let t':= E j
  have heB: Doors.rate ((H!).S.block m)= Doors.rate L':= congr_arg _ he'
  have hℓ: Real.exp ((H!).rep N n (m+1)).p.supportExponent = Real.exp (Rt).p.supportExponent:= by rw [ht]
  rw [heB,hℓ]; apply MergeProof.turnout («R»:=K z) ht he'
  refine ⟨fun i' hi'=>?_,fun f b c' h' hf=>?_, fun f j c' hcc hQ hF hS _=> ?_,?_⟩
  · have hwz:Heir.Release.accepts (B.span J T) (M.p.profile j).supportExponent ((M.p.profile i).supportExponent+2) L:= hC' _ _ d hb _ (D.large _).need|>.1
    exact jewelCard hm hP hp hc hb hV hC H z hz₀ hΨ i' g he ht hd h' hY hκ hi' T' hi hj hb' Xk (hx _ ankle) hwz
  · exact basalCard g hm hV hC hC' hw hd hY hκ H z ht he hΨ b c' f h' hf Xk (hx b h'.anchor)
  · exact heavyK g hm hV hC H z he ht hY hκ hq Xk j f c' hQ hcc hF (by assumption)
  have hσ: Planned.GuardedAtom.Forecast uP cap:= Cub.leading P' R₀ (sound G d) (Next.Foundations.valuation G d) W hi hj hb'
  have hh: Local.triangularPrice F cap ≤ E J:= (h' _ _ hz (first_le A.B.valid m) d hd).2 hj' hi hj
  intro i'; exact hσ.quote hh i'
end YM.PhysicalNext.Repeat.Cub
