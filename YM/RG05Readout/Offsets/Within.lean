import YM.RG05Readout.Offsets.Stable
import YM.RG05Readout.Offsets.Emit
import YM.UVExtension.Flake.Plaza
/-!
# Purchase consumer ports from actual Mark stock (adapt `clocksHere`)

Constructs ppT triangular certificate on the off-center domain,
including emitted flag reserves. Parameters on the SAME actual V path.
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
variable {K:In A.B.a m n} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
set_option quotPrecheck false
open PPX MergeProof Next.Free Bid
variable (he : (History.mk A.B.a jV).rep N n m=H.result z.val) (ht: (History.mk A.B.a jV).rep N n (m+1)=K z.val) (hRC : (History.mk A.B.a jV).Conv N n m) (g:G.Simple)
   (hC': Graces.Moms B.prices M.K B.span M.p.floorL)(hw: Graces.Cruise B.prices D B.recordP B.span B.shape A.delay) (hT: Cub.MainTest B.target B.expense B.span D B.shape C R A.delay)
   {E:ℕ→ℝ}(h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)
local notation "H!"=> History.mk A.B.a jV
local notation "DO"=> duet (History.mk A.B.a jV) N n m he ht (sandboxK H z)
local notation "Rt"=> K z
local notation "ε0"=> Cub.title G vT
local notation "Πt"=> localSection G d
local notation "Rc"=> H.result z
local notation "D0"=> sandboxK H z
local notation "H0"=> History.mk A.B.a jV
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
open RG05Cell
include hcV hΘ hg hP hp hc hb hV hC hC' hw hm hY h' hT he ht g hRC hκ
-- Tracker upper-loop budget.
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1150000 in
lemma RG05_price (D' : Angle J T d (vB).order L vB vT (query M.p M.K J T) M.p.kernel u v (B.target J T) (B.walls J T) (B.shape.o J T) (B.shape.μ J T) y (B.span J T))
    (hd:d+3≤T) : ∃ (P:Heading F) (a:ℝ),Pricing (localSection G d) (History.mk A.B.a jV) N n m (hol G)
       DO P a (E J) (Doors.rate L) (2*(Real.exp ((K z).p.supportExponent)*Cub.title G vT)) ∧ Local.triangularPrice F a ≤ E J:=by -- add params T₀
    let i:= T; let j:=J; let L':= D.L j; have h0:d ≤ i:= (Nat.le_add_right _ _).trans hd
    have hj := step_paid A.B.a m; have hy:d ≤ j := h0.trans hj.1
    have hm':(H0).S.block m=L:=PriceCompiler.block_eq A.B.valid m
    have hK: Mallow.Arrives B.shape A.delay:=hC
    have hwz:Heir.Release.accepts (B.span J T) (M.p.profile j).supportExponent ((M.p.profile i).supportExponent+2) L:= hC' _ _ d hb _ (D.large _).need|>.1
    obtain ⟨T'⟩:= hT _ _ (A.B.valid.pays m) i d (first_le A.B.valid m) hj hd
    let K₀:=A.B.a.budget m
    let K':=A.B.a.budget (m+1)
    have hY':PPX.Blend 2 K'.threshold K₀.threshold :=T'.scaleP _ _ rfl (Circlet.shifting (A:=A) (m:=m)).1
    have hs:= A.B.a.clock.adm m; have hj':=A.B.a.clock.adm (m+1); let P':=Warehouse.flight (History.mk A.B.a jV) N m; let k:= Seal.donne (localSection G d) (sound G d) M.p.kernel.penalty_pos hs (Next.Foundations.valuation G d) P' hy hY'
    let uP:= matrix (localSection G d) (sound G d) (Carrier.stored P' M.p.kernel.penalty M.p.kernel.penalty_pos hs) K'.threshold K₀.threshold
    let cap:= Seal.cap (localSection G d) (sound G d) M.p.kernel.penalty_pos hs (Next.Foundations.valuation G d) hj' hy (one_le_two (α:=ℝ))
    have hσ: Planned.GuardedAtom.Forecast uP cap := Cub.leading P' (localSection G d) (sound G d) (Next.Foundations.valuation G d) M.p.kernel hs hy hY'
    have hh: Local.triangularPrice F cap ≤ E J:= (h' _ _ hj (first_le A.B.valid m) d hd).2 hj' hs hy
    refine ⟨k,cap,⟨?_,?_,fun x=>hσ.quote hh x,PPX.Seal.cap_lead _ (sound G d) _ hs _ _ hy hY'⟩,hh⟩
    · intro b' hB'
      let Tq: Keeper (((H0).rep N n (m+1)).p) (((H0).rep N n (m+1)).activities) := ht.symm ▸ Keeper.sufficient hΘ
      let hyK: Keeper (((H0).rep N n m).p) (((H0).rep N n m).activities):= he.symm ▸ hg
      let Xk(i : {U:Support n₁ // b'∈ U}): Wing:= .logKey (Blush.found b' i.val i.property)
      let Yq(i: StockTag n₁): Wing:= .gasKey (cart (R:=(H0).rep N n (m+1)) Tq i)
      let Xq:= Set.range Xk ∪ Set.range Yq
      have hzn : Xq.Finite:= (Set.finite_range Xk).union (Set.finite_range Yq)
      refine ⟨Tq,Xq,hzn,fun m=> Or.inr ⟨m,rfl⟩,⟨fun i' hi=> ?_,fun f s c hx heP=> ?_,fun f s c hv hx hy ha=>?_⟩⟩
      · intro Yx p0 U0
        have hw₀:Xq (.logKey (tab G b' d)) := Or.inl ⟨⟨_,toe b'⟩,rfl⟩
        obtain ⟨u',hU,hF,hT',hs'⟩:= RG05_primary hm hP hp hc hb hV hC H z hcV hΘ b' hB' i' g he ht hd h' hY hκ hi hRC Xq hw₀ hyK D' hs (h0.trans hj.1) hY' hwz
        unfold U0; rw [hm',show p0.density b' (localSection G d) ((H0).rep N n (m+1))= _ from congr_arg (p0.density _ _) ht,
           show p0.exponentialEntry b' (localSection G d) ((H0).rep N n (m+1))= _ from congr_arg (p0.exponentialEntry _ _) ht]; refine ⟨u',hU,hF,hT',hs'.climb le_rfl ?_ le_rfl⟩
        have hc':=(K z)
        have hzeta := hc.buys _ _ hb.1 (first_le A.B.valid m) _ (A.B.valid.pays m) d (h0.trans hj.1)
        have hr:(K z).p=B₂:=(H.knows _ z.2).1.point
        have hr' : minSide G d ≤ (K z).p.B:=by rw [hr,(Circlet.shifting (A:=A) (m:=m)).2]; exact hzeta.geometry.2
        exact mul_le_mul_of_nonneg_left (RG05Cell.tally (K z) b' i' hcV hΘ hr') zero_le_two
      · rw [ht] at heP hx
        have h':= RG05_stable g hm hC hC' hw hd hY hκ H z ht he hΘ b' hB' hRC hyK s c f hx heP Xq (Or.inl ⟨⟨_,hx.anchor⟩,rfl⟩)
        -- transport Through via casting. rewriting under D parameter can fail
        convert h' using 1; rw [ht]
      rw [ht] at hv
      let d':=(K z).p.mass ((K z|>.activities.forced s).support) c
      let i:= κ
      -- can't rw under q1
      have h:= RG05_heavyK g hm hC H z he ht hY hκ h0 hyK b' hB' hRC Xq s f c hy hx hv ha
      unfold Along
      intro t u₁
      unfold u₁ t
      rw [hm',show Extra.Histories.fare ((H0).rep N n (m+1)) s f=_ from congr_arg (fun x'=>Extra.Histories.fare x' s f) ht,
          show exactGas ((H0).rep N n (m+1)).activities s f=exactGas (K ↑z).activities s f from congr_arg (fun R : Rep G n₁=>exactGas R.activities s f) ht,
          show ((H0).rep N n (m+1)).p=(K ↑z).p from congr_arg (·.p) ht,
          show (((H0).rep N n (m+1)).activities.forced s).support= _ from congr_arg (fun R:Rep G n₁=>(R.activities.forced s).support) ht]
      exact h
    exact sound_duet (H0) N n m he ht _ _ (sounds g hm H z hK)
end YM.PhysicalNext.Repeat.Cub
