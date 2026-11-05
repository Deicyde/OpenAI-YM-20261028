import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Natives
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Seams
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Petty

/-!
# E inherited and crown-edge labels

Keep fine and coarse parts with *true* betas and cuts. Reuse CAB factors at ZERO order, not their Y or accounting-mask formulas; these pay Pantry. No hair-cut growth implied for the output p. No post at a favorable lower P.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Ancestor
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Aff Cab Coverage Calls Win Bid Push.AbsoluteSums
    Dictionary AnalyticBridge.Annulus.Map Dictionary.Geo
    Exterior Next.Fluctuations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {c f n : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x W d t a C : ℝ} {B : ℕ} {p q : Pilot G S x} {X : Support c} {v : Dyed G S}
local notation "Z"=>radiusB x
lemma issueTop (h : Chips v P W x) {g : Config G f →ℝ} (he : Measurable g) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) : ShellView (fun V y=>g (v.top (x:=x) ⟨A,F,k,V,y⟩)):= by
  obtain ⟨w,hm,H⟩:= v.top_read h.boost h.arc_pos h.vista A F k; exact ⟨_,he.comp hm,fun V hp y=> congr_arg g (H V hp y)⟩

def gen (v : Dyed G S) (p:Pilot G S x) := - v.source.activities.additive v.source.p (v.top p)
-- regrade on v.bp.B! Actual threshold and both footprints.
lemma pre (h : Chips v P W x) (hp : 25*Z+30≤v.bp.B) (hR :v.source.activities.EBound v.source.p d)
    (hs : Footprint.reserve v.source.p.supportExponent a (Footprint.conversion S.ratio 1) t) (hv : v.source.p.B ≤ 2*v.bp.B): Petty v W v.bp.B a (Footprint.payment (S.ratio.count.val^4) (Footprint.extentCost 1 v.bp.B) 0 t 1 d a (Footprint.preCost 1)) (gen v (x:=x)):= by
  let R:=v.source; obtain ⟨w,hw,hA,hY⟩:= Labels.regular _ _ hR; let F i:= (R.activities.reg i).support; have hg i:0≤w i:=(hw i).1
  let Y i:= wings S v.bp.B (F i)
  obtain ⟨e',u,v',δ,g,H⟩:=h.lawful; let z i U:=R.activities.regularOccurrence R.p i U
  have hk i : Pulled (fun p:Pilot G S x=> -z i (v.top p)) (Y i):= by
    let f:=R.activities.E i
    let hS:= H.labels.regular.smooth i
    refine ⟨fun A F k=>issueTop (g:=fun U=> -z i U) h (Measurable.neg (masked_measurable _ _ _ hS.borel)) A F k,fun p q he hb hq=>?_⟩
    apply congr_arg Neg.neg; apply Coverage.Shed.mask_track _ f _ _ hS.sites; intro j hj _
    exact v.peak_record hq j h.boost.ready ((direct_beam (S:=S) hp (Next.Rank.Thirst.inspect (F i) hj)).shrink (by omega))
  have hb : Ac.Hit Y v.bp.B w a (Footprint.payment (S.ratio.count.val^4) (Footprint.extentCost 1 v.bp.B) 0 t 1 d a (Footprint.preCost 1)) := hY S.ratio 1 v.bp.B 1 _ _ zero_le_one hs v.bp.B_pos hv 0 w Y (fun i=> by simp [Y,wings, F, Footprint.enlargement,Labels.regularCore,R]) hg fun _=>by simp
  refine (Petty.accepts hk (fun i=> ⟨_,involved _ _ (R.activities.reg i).anchor⟩) hg hb hs.1 ?_).traded ?_
  · intro i p h; rw [abs_neg]; let U:=v.top p; by_cases he : Healthy R.p.threshold (F i) U
    · rw [show z i (v.top p)=R.activities.E i (v.top p) from masked_eq _ _ _ _ he]
      exact (hw i).2 _ he [] (Nat.zero_le _) (by simp)
    rw [show z i (v.top p)=0 from masked_ne _ _ _ _ he,abs_zero]; exact hg _
  exact fun p _ _=> (tsum_neg ..).symm
-- station conversions. +120 stencil uses both endpoints.
lemma squeeze (h : Chips v P W x) (hv:Hears X p q) {a:Support f} (i:Signed) (he : extent 120 ((a.image S.ratio.parent).image i.act) x ⊆ X) {j:Site f} (hj:j∈a) :
    AgreeNear S.ratio.parent (S.ratio.parent j) (Z/50+4) (pull i 0 (v.top p)) (pull i 0 (v.top q)):= by
  have hp : Shields X (i.act (S.ratio.parent j)) (120*Z) := fun u hu=> he (halo_spec.mpr ⟨_,mem_image_of_mem _ (mem_image_of_mem _ hj),hu⟩)
  apply Coverage.Shed.roll_fine; intro k hk; exact v.peak_record hv k h.boost.ready (hp.shift (by have hz:=h.boost.produced.scale; omega))
-- along Button
private lemma head (i:Buttons n) (Q:PathData G) (o:Clip) (t:ℝ) (l r :ℕ) : Measurable (chiffon Q o i l r t):= by
  -- Adapted from Canvas couple.
  let s:=i.1; let a:Cell n:= (i.2.2.1,i.2.1); have hm k : Continuous (fun U : Config G n=>Q.ellTerms a k U):= by unfold PathData.ellTerms Slot.atSite expandAt; fun_prop
  have hh : Measurable (pull i.1 0 : Config G n → Config G n):=(continuous_pull ..).measurable
  unfold chiffon drain; dsimp only; apply Measurable.ite _ ((Canvas.ip ((hm _).measurable.comp hh) ((hm _).measurable.comp hh)).div_const _) measurable_const
  by_cases he: strip Q a.2 l r i.2.2.2.1 ∧ strip Q a.2 l r i.2.2.2.2
  · unfold a at he; dsimp only at he; simp only [he,and_self,not_true_eq_false,and_false]; simp
  unfold a at he; dsimp only at he; simp only [he,not_false_eq_true,and_true]; exact hh (PathData.kept_closed ..).measurableSet
lemma strand (h : Chips v P W x) (hv : LaneCounts v.source.path x v.source.p.threshold v.source.clip C 1 S.ratio.parent) (i : Buttons f) : Pulled (fun p:Pilot G S x=> chiffon v.source.path v.source.clip i (till x) 1 v.source.p.threshold (v.top p)) (rib v.source.path S.ratio x i):= by
  let X:= fringe v.source.path i; refine ⟨fun B F k=> issueTop h (head ..) B F k, fun p q _ _ hp=>?_⟩
  have hg (j:Site f) (hb:j∈X):= squeeze h hp i.1 (Finset.Subset.refl (rib v.source.path S.ratio x i)) hb
  apply Coverage.Shed.for_rim _ i _ _ 1 S.ratio.parent (Work.E03.parent_step S) hv _ _ ?_ (hg _ (mem_insert_self _ _))
  exact fun i hi _=> hg i.1 hi i (by rw [separation_self]; omega)
lemma renew (h : Chips v P W x) (i : Buttons c) : Pulled (fun p:Pilot G S x=> chiffon v.things.down v.things.low i (till x) S.patch.L.val (temp x) p.view) (rib v.things.down (plain c) x i):= by
  refine ⟨fun A F k=> ⟨_,(head ..).comp measurable_fst,fun _ _ _=>rfl⟩, fun p q _ _ hp=>?_⟩
  let X:= fringe v.things.down i; let a:=i.1
  obtain ⟨u,hu⟩:= h.boost.produced.coarse
  have he (p:Site c) (hp:p∈ X): a.act p∈partWay v.things.down (plain c) i:= mem_image_of_mem _ (mem_image.mpr ⟨_,hp,collar p⟩)
  have hg j (hj:j ∈ X): AgreeNear id j (Z/50+4) (pull a 0 p.view) (pull a 0 q.view):= by
    apply read_turn; apply Geo.Reads.visit hp.reads
    exact fun w hw=> halo_spec.mpr ⟨_,he _ hj,hw.trans (by have ht:=h.boost.produced.scale; change _≤120*radiusB x; omega)⟩
  exact Coverage.Shed.for_rim _ _ _ _ _ (id:Site c→_) (fun i j=>Work.E03.sep_step i j) hu p.view q.view (fun i hi _=>hg _ hi i (by simp)) (hg i.2.2.1 (mem_insert_self _ _))
lemma chairmen (h : Chips v P W x) {k : ℕ} (R : ℕ→ Atom G k) (i : Lamps f) : Pulled (fun p:Pilot G S x=>(R i.2.2).placed v.source.p (pull i.1 0 (v.top p)) i.2.1) (article R S x i):= by
  let o:=i.2.1; let g:=R i.2.2; let z:=g.footprint o
  refine ⟨fun A F k=>issueTop (g:=fun U=>g.placed v.source.p (pull i.1 0 U) o) h ((masked_measurable _ _ _ (g.unmasked_cont ..).measurable).comp (continuous_pull ..).measurable) A F k, fun p q _ _ hp=>?_⟩
  exact Coverage.Shed.mask_track z _ _ _ (Coverage.Shed.for_atom g o) (fun j hj _=> squeeze h hp i.1 (Finset.Subset.refl _) (show j.1∈ inspected z from hj) j (by rw [separation_self]; omega)) _
end YM.PhysicalNext.InteractingRank.Pump.Ancestor
