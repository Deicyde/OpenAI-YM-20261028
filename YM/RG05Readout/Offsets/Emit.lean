import YM.RG05Readout.Offsets.Transport
import YM.UVExtension.Flake.Lamps
import YM.RG05Readout.Offsets.Target
import YM.RG05Readout.Offsets.Budget
import YM.RG05Readout.Offsets.Expansion
/-!
# An off-center primary input gives a real hierarchical output at anchored center

Mint the actual weighted support rep first (including wrap), on graph Pill for
any offset over 0. Then certify the output in its engineering rows which must
be inverted with care. No small projection bound on the residual higher rows,
and the heading is not a label transfer or an assertion of analytic discrepancy.
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
local notation "K!"=> K z.val
variable (hz:Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1))))) (h!:HasSlots (K z|>.p) (K z|>.activities))
-- wrap etc. earn with fixed Glider.
local notation "β" => (K z.val).beta
open RG05Cell
variable (b₀:Site (A.B.a.S.side (m+1) n))(hb₀:(A.B.a.clock.op m n).ratio.parent b₀=0)
local notation "Ω"=> RG05Cell.tab G b₀ d
local notation "w"=> B.span J T
local notation "Xp"=> (localSection G d).footprint b₀
local notation "Yp"=> (plate Z Ω).support
open PPX Next.Free WardBin.Lies
-- expose Leg without footing.Help alignment
variable (i:((Labels.frames G).level d).Index)
local notation "θ!"=> Cub.title G vT
local notation "T!"=> wood (K z) b₀ i hz h!
local notation "c0"=> (K z).p
local notation "U!"=> (X)
local notation "f!"=> RG05Cell.hills (K z) b₀ i
local notation "Z0"=> icon Z Ω
local notation "q'"=> Chi.canonical
set_option quotPrecheck false
include h! hm hP hp hc hb hV hC
include hb₀
open Multi.Puff Source Bid
local notation "M0"=> (M.p.profile T)
local notation "v0"=> ((L).val:ℂ)^d
local notation "F0"=> (Blush.pane Z T! v0 Z0)
local notation "t0"=> ((B₁).threshold)
local notation "S!"=> localSection G d
local notation "p'"=> (Vintage.YM.Planned.PrimaryIntegral295.WaterLevels.forecast V m N n)
local notation "f0"=> pupil H z (T!).live
local notation "f1"=> pupil H z (T!).pale
local notation "r0"=> Blush.screen Z T! f0 f1 v0 F
local notation "Scope"=> Blush.scope Z T! (0:Site n₀)
variable (g:G.Simple)
    (he : (History.mk A.B.a jV).rep N n m = H.result z.val) (ht : (History.mk A.B.a jV).rep N n (m+1) = K z.val) (hd : d+3≤ A.B.a.clock.J m) {E:ℕ→ℝ}
    (h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)(hi:i≠0)
local notation "yT"=> authors A.B.a m
include he ht hd h' hY hκ hi g
local notation "Wk"=> History.mk A.B.a jV
local notation "W₁" => (Wk).rep N n m
open MergeProof Guard YM.RG05Readout.Offsets
set_option maxRecDepth 6000 in
set_option maxHeartbeats 960000 in
lemma RG05_primary (Hk:(Wk).Conv N n m)(Pa:Wing→Prop)(hW:Pa (.logKey Ω))(Tq : Guard.Keeper ((History.mk A.B.a jV).rep N n m).p ((History.mk A.B.a jV).rep N n m).activities) (D':Angle J T d (M0).order L vB vT (query M.p M.K J T) M.p.kernel u v (B.target J T) (B.walls J T) (B.shape.o J T) (B.shape.μ J T) y (B.span J T)) (hs:4≤ A.B.a.clock.J m) (hj:d ≤ A.B.a.clock.J (m+1)) (hJ:Blend 2 (B₂).threshold (B₁).threshold)
    (hv:Heir.Release.accepts w (vT).supportExponent ((vB).supportExponent+2) L):
    let P:=Warehouse.flight (History.mk A.B.a jV) N m; let Zx:=Seal.donne S! (sound G d) M.p.kernel.penalty_pos hs (Next.Foundations.valuation G d) P hj hJ; let x:= Size.axis F i
    let p:= Extra.Histories.primary b₀ x
    let O:= (W₁)
    let c:= E J*(F).coeffSize (vowel F L ((F).core x))
    ∃ Q:Coefficient F n₀, Gig S! (Wk) N n m (hol G) (p.density b₀ S! (K z)) Q Q.x 0 c ∧
        (F).coeffSize (basisCut F ((F).grades i).1 (Q.x-Zx.leads L x)) ≤ Doors.rate L ∧
        (F).coeffSize Q.x ≤ c ∧
        Tale Pa b₀ 0 v0 (p.exponentialEntry b₀ S! (K z)) 0 (profile O.activities Q.forced) 0 (2*load (T!).live) c (duet _ _ _ _ he ht (sandboxK H z)):=by
  intro P Z' Y qPrim O c₀; let U:=wood (K z) b₀ i hz h!; let I:= enter (Z) (Z0); let R₁:=Blush.scope Z T! (0:Site n₀); let M':= (r0); let R':=(History.mk A.B.a jV).rep N n m
  have hP':d ≤ T:= (Nat.le_add_right d 3).trans hd
  have hS:=lively hY hP' (n:=n)
  have hx: R'.p=B₁:=by rw [show R'=H.result z from he]; rfl
  have hb₃:=RG05_target hm hP hp hc hb hV hC H z hz h! b₀ hb₀ i D' hS
  obtain ⟨a,b,c,hA,hR,hT,hsy,hp⟩:= RG05_budgetLoop hm hP hp hc hb hV hC H z hz h! b₀ hb₀ i hi g he ht hd h' hY hκ Tq hv
  let x:= Z'.leads L Y; let f:= M'.row 0 R₁ (hol G) t0
  have hZ: M'.Format 0 R₁ R':=hA.1
  have hsI: R₁ I=Yp:=by unfold R₁ Blush.scope I; rw [(enter Z).injective.extend_apply]; exact Mercury.grinchY Z (T!).live Ω rfl _
  have hI:f I = Local.weighted (hol G) F 0 Yp t0 F0:=by unfold f Push.Local.Raw.row; rw [hsI]; change Local.weighted _ _ _ _ _ (stuff (enter Z) _ (enter Z _))= _; rw [stuffed]
  have hTg:=(costs_rows (F) ((F).grades i).1 (f I-x) _ D'.later (fun p h hi=> by rw [hI]; exact hb₃.2 p h hi hs hj hJ))
  have hΨ:= hC _ _ (A.B.valid.pays m) _ hb.1|>.1
  obtain ⟨p₁,b₂,y₀,gP,v₀,Y',g₁,C',g',e,uc,hX,hQ,N'',hη⟩:= hΨ.2 _ _ _ _ (Opera.protocol A.B hm B.pledging.conducts.full) _ _ Z
  have ho:= Rain.jersey (A:=A) (m:=m)
  have hS':0∈ U.live.crest.image (X).ratio.parent:= Finset.mem_image.mpr ⟨b₀,(by unfold U; rw [RG05Cell.place]; exact toe _),hb₀⟩
  have hY': (B₁).supportExponent+2≤(B.expense J T).earn:=by rw [ho.2.2.1]; have h:=B.pledging.agenda _ _ hb.1|>.1; linarith
  obtain ⟨hz',hq⟩:= Cub.brimmed Z (T!) 0 f0 f1 v0 F N'' hη hΨ.1 hX rfl rfl ho.1 hY' (ho.2.1.symm ▸ hQ) hS' (i:=Ω) rfl (hol G) hx hZ hS
  let V':= (fun j=> if j=I then 0 else f j); have hF:f = V' + fun j=> if j=I then f I else 0 :=by ext j; by_cases hz:j=I<;> simp [hz,V']
  let K1:ℕ→ ((F).Coeff) := fun j=>if j=I then f I else 0
  have hK : HasSum K1 (f I):=hasSum_ite_eq _ _
  have hv: Summable V':=by
     have ht: Summable (V' + K1):= congr_arg (fun Zα : ℕ → (F).Coeff => Summable Zα) hF ▸ (show Summable f from hz') -- likely rw all
     have hh : Summable ((V'+K1)-K1) := ht.sub hK.summable; rw [add_sub_cancel_right] at hh; exact hh
  have hf:∑' j,f j=(∑' j,V' j)+f I:=by
      calc ∑' j,f j=∑' j,(V'+K1) j:= tsum_congr (fun i=>congr_fun hF i)
           _ = _:= (hv.hasSum.add hK).tsum_eq
  let v₀:= marvel (Q:=B.target J T) («L»:=D.L J) (x:=y) U; let u0:=‖v0‖*(v₀+v₀)
  let p₀:= Local.testPrice (F)*D'.current+Local.readPrice (hol G) (F)*u0
  obtain ⟨S⟩:=hR
  let U0:= Guard.mint S M' (hol G)
  have hκ' :0< Push.Local.kappa (Wk) m:= Real.sqrt_pos.mpr (forcedPos ..)
  have hS₀ : Local.Readable (hol G) (localSection G d) O.p n₀ yT := (show O.p = B₁ from hx).symm ▸ hS
  have h₀ :=Guard.usage S hA.1 Hk.good hS₀
  have hft : U0.density _ (localSection G d) O= blast (Wk) N n m d U.milk:= (value_mint S hA.1 Hk.good hκ' hS₀ hT).trans hA.2
  have hfR: qPrim.density b₀ S! (K z)= U.milk:=by
     refine Eq.trans ?_ (Blush.balm (K z) b₀ Xp (toe _) _ _ (RG05Cell.costs (K z) b₀ i hz).1 (RG05Cell.costs (K z) b₀ i hz).2 h!)
     funext V; rw [primary_density]; unfold Extra.Histories.salary
     change ((K ↑z|>.eval V):ℂ)*(Y 0+masked (K z|>.p).threshold Xp ((S!).places (F|>.scaled (K z|>.p).threshold⁻¹ ((F).core Y)) b₀) V)=_
     unfold Y; rw [Size.core_axis,if_neg hi,show Size.axis F i 0=0 from Pi.single_eq_of_ne hi.symm _,zero_add]
     rfl
  have hr:= tab_mint S hA.1 Hk.good hκ' hS₀ hT
  have hs₁ : 1 ≤ Local.turnCost O.p.order O.p.power := one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
  have hrs:= (le_mul_of_one_le_left hr.first hs₁).trans ((le_add_of_nonneg_right hr.second).trans hp)
  refine ⟨U0,⟨h₀,hfR.symm ▸ hft,(by rw [sub_self,show (F).coeffSize 0=0 from (by simp [Frame.coeffSize]),mul_zero]),_,_,hr,hp⟩,?_,?_ ,?_⟩
  · change (F).coeffSize (basisCut F ((F).grades i).1 (U0.x-x)) ≤ _
    have heM : U0.x = (∑' j,V' j)+f I := by
       change M'.seed+ (∑' i,M'.row 0 _ (hol G) R'.p.threshold i)=_
       rw [hx,show M'.seed=0 from rfl,zero_add]
       exact hf
    rw [heM,add_sub_assoc,map_add]
    have hUX : (F).coeffSize (basisCut F ((F).grades i).1 (∑' j,V' j)) ≤ Local.readPrice (hol G) F*u0 := (cap_rows ..).trans hq
    apply (Size.add F _ _).trans ((add_le_add hUX hTg).trans ?_)
    have hΞ:=(K z)
    let Z₁:=(K z).p.mass U.live.crest U.live.weight
    have hB:(K z).p=B₂:=(H.knows _ z.2).1.point
    have hr:=hc.buys _ _ hb.1 (first_le A.B.valid m) _ (A.B.valid.pays m) d hj|>.geometry.2
    have hz₀: Z₁ ≤ credibility G (vT).supportExponent (vT).order (vT).power:= (RG05Cell.tally (K z) b₀ i hz h! (show minSide G d ≤(K z).p.B from by rw [hB,(Circlet.shifting (A:=A) (m:=m)).2]; exact hr)).trans_eq (by rw [hB, Rain.jersey (A:=A) (m:=m+1)|>.2.2.1]; rfl)
    have h := D'.pricedC _ hz₀ n₁ (K z) U rfl
    rw [add_comm]
    unfold u0; rw [show ‖v0‖=((L).val:ℝ)^d from by simp,← two_mul]; exact h
  · have h:= size_mint S hA.1 hS₀ hT 0
    change (F).coeffSize (U0.x-0) ≤ (F).coeffSize (M'.seed-0)+a at h
    rw [show M'.seed=0 from rfl, sub_zero,sub_zero,show (F).coeffSize 0=0 from (by simp [Frame.coeffSize]),zero_add] at h
    exact h.trans hrs
  · obtain ⟨e,l,hq,h₃⟩:= hsy
    have hA' := vigor hq hA.1 hS₀; rw [h₃] at hA'
    have hU:= stackFee hA' hrs
    have he' := budgetProfile S hT hA.1 hS₀ Hk.good hκ'
    apply peels (Wk) N n m he ht (sandboxK H z) _ _ _ _
        _ _ _ _ _ _
    let V₂:= profile (H.result z|>.activities) U0.forced
    let X':= coda S! (hol G) 0 R₁ M' R'
    apply RG05_expansion g hm hC H z U U.rates b₀ Pa hW _ _ X'
        (by unfold U; rw [RG05Cell.place]; exact toe _) _ _ V₂ _ _
    · let F':=RG05Cell.hills (K z) b₀ i; let O':=masked (K z).p.threshold (Xp) F'
      have hv: qPrim.exponentialEntry b₀ S! (K z) = O':=by
        funext V; unfold qPrim; simp only [Extra.Histories.primary,Coefficient.exponentialEntry]; unfold Y; simp_rw [Size.core_axis (F),if_neg hi,show Size.axis (F) i 0=0 from Pi.single_eq_of_ne hi.symm _,zero_add]
        change O' V + ∑' j, qPrim.maskedTerm (K z) j V= O' V
        have hh j:qPrim.maskedTerm (K z) j V=0:= congr_fun (map_zero (Push.Local.maskLinear _ _)) V
        simp_rw [hh,tsum_zero,add_zero]
      rw [hv]
      funext j; change _ = (↑(O' j).re:ℂ)+Complex.I*↑(O' j).im; rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
    · funext m U; change (0:ℂ)=0+Complex.I*0; simp
    · change V₂= _ + hook _ _ X'; unfold V₂; rw [← he]; exact he'
    rw [← he]; exact hU
end YM.PhysicalNext.Repeat.Cub
