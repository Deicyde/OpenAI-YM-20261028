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
include hp hm hP hV hb hC
set_option maxHeartbeats 800000 in
lemma mire (I: Medal G J T d (M0).order L vB vT M.p.kernel u v (B.target J T) (B.walls J T) (B.shape.o J T) (B.shape.μ J T) y ξ₀ z' (B.span J T)) (F':Leaf (K z))(ρ : Config G n₁→ℝ)(j:ℕ) (hδ:F'.turn=.logKey j)(hω:F'.ingredient=masked (q0).threshold ((K z).activities.reg j).support ρ)(hy: coverNumber (B₁).B (plate Z j).support≤(B₁).B)
    (hΩ: ((K z).activities.reg j).site=(0: Site n₁)) (h: (q0).Regular ((K z).activities.reg j).support ρ)(hF:(q0).supBounds 0 ((K z).activities.reg j).support ρ F'.weight)
    (hL:20*(radiusD y+Heir.reach y+1)<(n₀).val)(hξ: Nonwrapping ((K z).activities.reg j).support 0→Peak.lit 0 ((K z).activities.reg j).support ρ d) : let U:=matin F' Z (icon Z j) Chi.canonical; let p:=(plate Z j).support; let R:=dimW (0:Site n₁) (Malachite.radiusD y) (WaterLevels.forecast V m N n) ρ; let x:=sprite G y L z'
    (B₁).Regular p U ∧ Nonwrapping p 0 ∧ Local.Chart d U 1 ∧ Local.Chart d R 1 ∧ (∀ l:List (Directions G n₀), l.length ≤ d→ (∀ A∈l,(B₁).dirBound 0 A)→ ‖leftDerivs U l 1-leftDerivs R l 1‖ ≤ (x+x)*F'.weight) ∧
     ∀ p∈Local.tests F, ‖iteratedDeriv p.2.val (R ∘ (hol G).testLinks d 0 (t0 • p.1)) 0‖ ≤ x*F'.weight :=by
   intro U p₀ f ξ'
   have hr:= Rain.jersey (A:=A) (m:=m); let f0:=(K z).activities.reg j; have hS := (H.knows _ z.2); have hB:(q0)=B₂:= hS.1.point
   have ht: (plate Z j).site=0:=by change (X).ratio.parent ((K z).activities.reg j).site=0; rw [hΩ,anchor0]
   obtain ⟨hA,hR⟩:= united (n:=n) hm hP hp hV
   rw [← hB] at hA hR
   let κ:= I.eve
   have hΨ:= hC _ _ (A.B.valid.pays m) _ hb.1|>.1
   obtain ⟨p₁,b₂,y₀,gP,v₀,Y',g₁,C',g',e,uc,hX,hQ,N'',hη⟩:= hΨ.2 _ _ _ _ (Opera.protocol A.B hm B.pledging.conducts.full) _ _ Z
   have hd : d ≤ (M0).order := Nat.le_of_lt hb.2.1
   have hz:=I.leader; have hJ : ((K z).p.B)= radiusB (betaF G y L):= by rw [hB]; exact (Circlet.shifting (A:=A) (m:=m)).2
   have hv:(K z).p.power=(vT).power:=by rw[hB]; exact (Rain.jersey (A:=A) (m:=m+1)|>.2.1)
   have he: (K z).p.threshold=fiery G y L:=by rw [hB]; exact (Circlet.shifting (A:=A) (m:=m)).1
   have hx: (B₁).threshold=temp y:=rfl
   have hμ:=κ.scaleP B₁ q0 hx he
   have hτ₁: (B₁).threshold ≤ 2*(q0).threshold:= (div_le_iff₀ hμ.fine).1 hμ.accounted
   obtain ⟨hl',hx,hn,hh⟩:= hz.buoy B₁ q0 hr.2.1 hv he hτ₁
   letI : Nonempty (Forest (X).ratio):= Tree.select _ (X).patch.odd_side; let W:= Classical.arbitrary (Forest (X).ratio)
   let a:=mapcase Z j W
   have ha (i:Site n₁)(hx:i∈f0.support):halo (Heir.reach y) {(X).ratio.parent i} ⊆ p₀:= (Corona.halo_mono (Nat.le_add_right _ _) (Finset.Subset.refl _)).trans (a.asks i (Finset.mem_union_left _ hx))
   have hY:(X).patch.L=L:= PriceCompiler.block_eq A.B.valid m
   obtain ⟨hp,hk⟩:= foliageK p₀ f0.support B₁ L 0 0 u v ⟨f0.site,f0.anchor⟩ hY rfl hy (show (X).ratio.parent f0.site∈ p₀ from (plate Z j).anchor) hz.dawn hl' hx hn hh (hJ.symm ▸ hz.hit) ha
   have hf:∀ x∈ p₀,separation 0 x≤ radiusD y:=by intro x hx; rw[← ht]; exact hp.feasible _ hx
   have hsize:Nonwrapping f0.support 0:=by
       intro i hi
       have hh:= facesBound (S:=X) ha hf _ hi
       have ha:0 < (L).val:=(L).property; change separation i 0 ≤depthW (X).patch.L (radiusD y) at hh; rw [hY] at hh; unfold depthW at hh
       calc
          _ ≤ 10*(_):= Nat.mul_le_mul_left _ hh
          _ = 10*(radiusD y+2)*(L).val:=by ring
          _ < (n₀).val*(L).val:=Nat.mul_lt_mul_of_pos_right (by omega) ha
          _ = _:= by rw [← hY]; exact (X).sizes.symm
   have ht':Nonwrapping p₀ (0:Site n₀):=fun i hi=>by have he:=hf i hi; rw [separation_comm _ i] at he; exact (show 10*separation i 0 <(A.B.a.S.side m n).val from (Nat.mul_le_mul_left 10 he).trans_lt (show 10*radiusD y<(A.B.a.S.side m n).val from by omega))
   have hy:= I.leader.stirred β ((by rw[← PriceCompiler.beta_eq A.B.valid]; exact hS.2.1)) n₁ f0.support _ _ he hτ₁ (hJ.symm ▸ hz.cut) hr.2.1 hk
   obtain ⟨hT,hx⟩:= hy
   have hw:= Mercury.cornice Z F' j hδ v Chi.canonical N'' hA hη hr.1.le
   have hp' : Push.Local.Chart d U 1:= (hw.smooth _ (one_healthy _ _ (B₁).threshold_pos.le)).of_le (Nat.cast_le.mpr (hd.trans hr.1.symm.le))
   have hz:Push.Local.Chart d f 1:=(Quince.dimW_focus (o:=0) (m:=radiusD y) hR h).germ.of_le (Nat.cast_le.mpr hd)
   refine ⟨hw,ht',hp',hz,fun l hl he=>?_,fun p hₚ=>?_⟩
   · have hh := anthemW Z F' j hδ v Chi.canonical Chi.canonical 1 N'' hη ρ h hω hA (hr.2.1.symm ▸ κ.sails) rfl hr.1.le (B.pledging.agenda _ _ hb.1|>.2.2) (by assumption) (hΩ.symm ▸ hF : (q0).supBounds ((K z).activities.reg j).site ((K z).activities.reg j).support ρ F'.weight) hp hR (fun i j' => muse V _ _ _ _ _ _ _ _) hT hb.2.1 l hl (ht.symm ▸ he)
     rw [hΩ] at hh; let Z':= F'.weight; apply hh.trans; apply le_trans (add_le_add (a:=Z'*κ.sail) (mul_le_mul_of_nonneg_left I.sail F'.profit) (hx _ F'.profit)); apply le_of_eq; unfold ξ'; ring
   let P':=Warehouse.flight (Issue.trail V) N m
   have hr:P'.L=(X).patch.L:=rfl
   have ht : HEq (p').R.A0 (Carrier.linesOf P' M.p.kernel.penalty):= by change HEq (Carrier.linesOf P' A.B.a.clock.kernel.penalty) (Carrier.linesOf P' _); rw [A.B.valid.kernel]
   exact I.leader.stand p hₚ B₁ q0 hμ hA.rehearsed.orders _ _ X p' f0.support p₀ hY ha hf hL P' (hr.trans hY).symm ht _ _ h hF (hξ hsize)
end YM.PhysicalNext.Repeat.Quince
