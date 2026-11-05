import YM.UVExtension.Harvest.Patch
import YM.UVExtension.Forest.Glue
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Harvest
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open MeasureTheory Push GridApprox Mast Steady
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "π"=> localSection G d
local notation "O!"=> hol G
open Metric Wet Wren
variable {V:Org.Bolt A}(a:Upland.Arc Q S V)
variable (x:Rose S)(hv : Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val))
open Relay Mast.Cellar Steady Push GridApprox Accent Cells

variable {t:ℕ→ℕ}{S v R} (U:Cellar S t R) (K:ℕ→ℕ)(h:Scrim (U.yard v) W (far A.B.a) (waybill A.B.a) (near A.B.a) (renal A.B.a) (Legato.Bandage.fly A.B.a) (mutt A.B.a K) (Orchard.roof S v))
    (hK: Stock.Tabs A.B.a) (J k:ℕ)(w:ℝ)(hw:0<w)(hz:Stock.Tabs.opens A.B.a 1 J m)
local notation "C0"=> yard v U
local notation "F"=> (C0|>.labels.level d)
local notation "K0"=> lensScope C0 d
local notation "o!"=> (0:Site ((C0).side k n))
local notation "T!"=> A.B.a.S

open Extraction OS RelayDifference
-- lift across registry J.Spectrum. retain rates eventually.M
open Hearth Next.Extract Dash Org
variable (hp:∀ v,Scrim (U.yard v) W (far A.B.a) (waybill A.B.a) (near A.B.a) (renal A.B.a) (Legato.Bandage.fly A.B.a) (mutt A.B.a K) (Orchard.roof S v)∧ Extraction.Wcmain (U.yard v))
include hK hp a
lemma ripeP (I:Shot (roster U))(hz: Extraction.suitable A.B.a.S n I.f)(k:ℕ→Rose S)(hk:Tendsto (fun i=> (k i).val) atTop (𝓝 0)) : UVExtension.Arrives (fun i=> Hearth.snapshot i n U (k i) d I):=by
   let v' : Orchard.Keys S:= fun n _=> k n; let P:=yard v' U; obtain ⟨Q,hQ,h⟩:= setP a U K (hp v').1 hK (hp v').2 (fun _=> ⟨rose0 S,hk⟩)
   let ht:=Vintage.YM.Extraction.Wcmain.projects P Extraction.Order.full (intakeV v' U) (hp v').2
   have he:= arriveShots hQ (Vintage.YM.Extraction.Around.size_done (intakeV v' U) (ht.book _ _)) n d I hz
   apply he.copy; filter_upwards [eventually_ge_atTop (t d), eventually_all.mpr fun j=> eventually_ge_atTop (t (I.left j).fst)] with i hi hh; exact slipP d i n U v' I hi hh
local notation "R'"=> Mast.roseA S
local notation "q0"=> yard (Mast.roseA S) U
include hp hK
lemma fairs (hs:Slicing (yard (Mast.roseA S) U) d n) : ∃ δ:ℝ,0 < δ∧∀ v:Keys S, (∀ᶠ i:ℕ in atTop,|(v i n).val|≤ δ) → Slicing (yard v U) d n:=by
   let C':= yard (Mast.roseA S) U
   let W (P:Keys S): Prop:=∃ (I:Finset (Shot (roster U))) (c:ℝ)(X:Submodule ℂ ((roster U).Ref d)),0<c∧(∀ i∈I,suitable A.B.a.S n i.f)∧ Module.finrank ℂ X+ charge G d=Module.finrank ℂ ((roster U).Ref d)∧ ∀ᶠ j in atTop,∀ x∈X,c*‖x‖ ≤ ∑ i∈I,‖portrait j n U P d i x‖
   have e(v:Keys S): Slicing (yard v U) d n ↔ W v:=by rfl
   rw [e] at hs; simp_rw [e]; obtain ⟨I,c,X,hc,hI,hX,H'⟩:= hs
   let J: Finset (Shot (roster U)):=I; let A' (i j):= snapshot i n U (rose0 S) d j
   choose! T hT using fun i (hi:i∈I)=> ripeP d n a U K hK hp i (hI i hi) (fun _=>rose0 S) (show Tendsto _ atTop _ from (tendsto_const_nhds (x:=(0:ℝ))))
   have hm (i) (hi:i∈J):∃ δ:ℝ,0<δ ∧∀ᶠ N in atTop,∀ z:Rose S,|z.val|≤δ → dist (snapshot N n U z d i) (T i)< (c/4)/(J.card+1):= stitched Subtype.val (rose0 S) rfl (ripeP d n a U K hK hp i (hI i hi)) _ (hT i hi) _ (by positivity)
   choose! δ hδ hK using hm
   have hδ' :∃ a:ℝ,0<a∧∀ i∈J,a ≤ δ i:=by
       by_cases h:J.Nonempty; · exact ⟨J.inf' h δ,(Finset.lt_inf'_iff h).2 hδ,fun _ hi=> Finset.inf'_le δ hi⟩
       exact ⟨1,one_pos,fun i hi=> (h ⟨i,hi⟩).elim⟩
   obtain ⟨δ',he,hv⟩:= hδ'
   let H0:= roster U
   let B:= (c/4)/(J.card+1)
   have ht (v:Keys S)(hh:∀ᶠ i:ℕ in atTop,|(v i n).val| ≤ δ'): ∀ᶠ N in atTop,∑ j∈J,‖T j-portrait N n U v d j‖ ≤ c/4 :=by
       have hr j (hj:j∈J): ∀ᶠ i in atTop, ‖T j-portrait i n U v d j‖≤B:=by
          filter_upwards [eventually_ge_atTop (t d), eventually_all.mpr (fun i=>eventually_ge_atTop (t (j.left i).1)), hh,hK _ hj] with i hi hn hp hq
          rw [slipP d i n U v j hi hn,norm_sub_rev]; exact (by apply le_of_lt; rw [←dist_eq_norm]; exact hq (v i n) (hp.trans (hv j hj)))
       filter_upwards [(eventually_all_finset J).mpr hr] with N hN
       apply le_trans (Finset.sum_le_sum (fun j hj=> hN j hj)); rw [Finset.sum_const,nsmul_eq_mul]
       unfold B; field_simp; linarith only [hc]
   -- read potency from T
   have hN (x:(roster U).Ref d)(hx:x∈X): c*‖x‖ ≤ ∑ j∈J, ‖T j x‖:=by
       have hk j (hj:j∈J): Tendsto (fun i=> portrait i n U (roseA S) d j) atTop (𝓝 (T j)):= (hT j hj).congr' (by filter_upwards [eventually_ge_atTop (t d), eventually_all.mpr fun i=> eventually_ge_atTop (t (j.left i).1)] with i hi h; exact (slipP d i n U R' j hi h).symm)
       exact ge_of_tendsto (tendsto_finsetSum J fun j hj=> (Dash.arcing (hk j hj) (tendsto_const_nhds (x:=x))).norm) (H'.mono fun i hi=> hi x hx)
   refine ⟨δ',he,fun v hh=> ⟨J,c/2,X,half_pos hc,hI,hX,?_⟩⟩
   filter_upwards [ht v hh] with i hi x hx
   have hw:=Finset.sum_le_sum (s:=J) (fun j _=> (norm_le_norm_add_norm_sub' (T j x) (portrait i n U v d j x)).trans (add_le_add_right (show ‖T j x-portrait i n U v d j x‖ ≤ ‖T j-portrait i n U v d j‖*‖x‖ from (T j-portrait i n U v d j).le_opNorm _) _))
   rw [Finset.sum_add_distrib,←Finset.sum_mul] at hw; change c/2* ‖(x:(roster U).Ref d)‖ ≤ ∑ j∈J, ‖portrait i n U v d j x‖; linarith only [hw,hN x hx,mul_le_mul_of_nonneg_right hi (norm_nonneg x),mul_nonneg hc.le (norm_nonneg x)]
end YM.UVExtension.Harvest
