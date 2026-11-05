import YM.SharpGram.Matrix.Leading
import YM.UVExtension.Rainfall.Ascot
/-!
# The *same* leading matrix for the UVExtension's actual singleton.

Lacing.Tribe uses `Tips`, which only retains a heading with certain bounds.
Recover the exact diagonal information proved hidden inside `Cub.pomp` (adapted
argument from Rainfall/Ascot, via `starry` for nonzero columns). Needn't redo
its remainder operator bound (`Tips.counts`, independent of heading).
-/
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
variable {N': RoutesF ((Labels.frames G).level d) (A.B.a.S.side m n) (A.B.a.S.side (m+1) n) (K z|>.p) (H.result z|>.p) (hol G)} (hN: Waged H z hcV hΘ hg N') -- hcV binder.notations Lean
include g hV hκ he ht hC hC' hw hm hY
include hN hT hP hp hc hb h'
local notation "Ψ"=> 2*(Real.exp ((K z).p.supportExponent)* Cub.title G vT)
local notation "T0"=> localSection G d
set_option maxRecDepth 6000 in
set_option maxHeartbeats 900000 in
lemma calibratedTips (hd : d + 3 ≤ T) (hz : 0 ≤ E J) :
    ∃ U : Heading F, SharpGram.ThresholdDiagonal F U (B₂).threshold (B₁).threshold ∧
      (∀ x, (F).coeffSize (U.map x) ≤ E J * (F).coeffSize x ∧
        (F).coeffSize (U.map.symm x) ≤ E J * (F).coeffSize x) ∧
      Tips N' L U rR (E J) := by
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
    have hlead : Local.Leading k.map.toLinearMap cap :=
      Seal.cap_lead R₀ (sound G d) W'.penalty_pos hi (Next.Foundations.valuation G d) P' hj hb'
    refine ⟨k, ⟨⟨cap,hlead⟩, fun i' j' h => ?_, fun i' j' h => ?_⟩, fun x => ?_, ?_⟩
    · exact through R₀ (sound G d) P' W'.penalty W'.penalty_pos hi hj a b i' j' h
    · exact later_only R₀ (sound G d) P' W'.penalty W'.penalty_pos hi
        (Next.Foundations.valuation G d) a b i' j' h
    · -- use only the proved pre-slot leading triangular price
      have hlim : Local.triangularPrice F cap ≤ E J := (h' _ _ hF (first_le A.B.valid m) d hd).2 hj' hi hj
      have hlim' := mul_le_mul_of_nonneg_right hlim (Work.G08.size_nonneg (F) x)
      refine ⟨(hlead.cost x).1.trans hlim', ?_⟩
      have hx := (hlead.cost (k.map.symm x)).2
      rw [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] at hx
      exact hx.trans hlim'
    obtain ⟨_,_,U',_,hv,_⟩ := pomp hm hP hp hc hb hV hC H z he ht g hC' hw hT h' hY hκ hcV hΘ hg hN hd hz
    refine ⟨hv.counts,hv.wing,hv.hush,fun l=>?_⟩
    rcases eq_or_ne l 0 with rfl|hh
    · -- every Heading agrees on this column (don't accidentally price 1 twice)
      have hq (U : Heading F) : U.leads L (Size.axis (F) 0) = ((L).val : ℂ)^d • (F).e0 := by
        change U.map (vowel (F) L (Place.copy (F) 0)) = _
        rw [vowel_col, map_smul, show Place.copy (F) 0 = (F).e0 from rfl, U.unit, Frame.zero_degree, Nat.sub_zero]
      have hx := hv.speed 0
      dsimp only at hx ⊢
      rw [hq U'] at hx
      rw [hq]
      exact hx
    have hu := UVExtension.Rainfall.alarm _ _ _ _ _ _ _ _ he.symm hg (hℓ l hh).2
    dsimp only at hu ⊢
    rw [hN.pace l hh]
    exact ⟨hu.earns, hu.rain, hu.stem⟩
end YM.PhysicalNext.Repeat.Cub
