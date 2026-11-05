import YM.Extra.MULTISOURCE_BOUNDS.Merger
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Desk
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Hulls
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Pot
/-!
# Value stream from `opacity` Drows at all directions. t_f retimed, do not
send F through OLD `threshold`. Keep occurrence ownership geometry at point tax.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Coffer
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticBridge.Annulus AnalyticBridge.Annulus.Map AnalyticNext.ConnectedActivity Aff Dictionary Dictionary.Geo Milk Exterior
open Bid
    Next.Fluctuations
open _root_.YM.SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x W t e b L : ℝ} {B : ℕ} {p q : Pilot G S x} {X : Support c} {v : Dyed G S}
lemma hold_outer (h : Chips v P W x) {C : ℝ} (hC : LaneCounts v.things.up x v.source.p.threshold v.things.high C 1 S.ratio.parent)
    (i : Milk.Grain S) (hy : Shields X (grantPlace S i) (64*radiusB x)): Pulled (fun p:Pilot G S x=> Milk.outer v.things x p.view p.tag v.source.p.threshold (v.top p) i) X:= by
  let T:= v.things; let t:= v.source.p.threshold; let s:=i.1
  refine ⟨fun A F k => ?_, fun p q hp hq hV=>?_⟩
  · obtain ⟨g,hm,H⟩:= v.top_read h.boost h.arc_pos h.vista A F k
    refine ⟨fun a=> Milk.outer v.things x a.1 k t (g a) i,?_,fun V hp y=> congr_arg (fun Q=>Milk.outer v.things x V k t Q i) (H V hp y)⟩
    let U:= (pull s 0) ∘ g; let V:=fun a: Config G c × RoomView A x F G=> pull s 0 a.1; let Q:=fun y=> S.prediction (U y) (choice s k)
    have hu: Measurable U:= (continuous_pull _ _).measurable.comp hm
    have hv : Measurable V:= (continuous_pull _ _).measurable.comp measurable_fst
    have he : Measurable Q:= (S.prediction_meas h.boost.produced.branched _).comp hu
    let hf := h.boost.funded; have ht : 0≤temp x:= temp_nonneg _
    rcases i with ⟨s',i|i|i|i⟩
    · exact Fabric.fine hf ht _ hu hv i
    · exact Fabric.bond hf ht hv he i
    · obtain ⟨a,b,c⟩:=Fabric.levels (R:=till x) hf ht hu hv he i; exact a.add (b.add c)
    exact Fabric.moment hf ht hv i
  let j:=seedPlace S i.2; let o:= s.act j; let r:=radiusB x
  have hr:120≤r:=h.boost.produced.scale
  let V:=p.view; let V':=q.view;let Q:=pull s 0 V; let Q':=pull s 0 V'; let U:=v.top p; let U':=v.top q
  have hv: AgreeNear id j (4*r) Q Q':= read_turn s j (4*r) _ _ (Geo.Reads.visit hV.reads (hy.shrink (by omega)))
  have he:TagNe S j (4*r) (choice s p.tag) (choice s q.tag):= TagNe.pull s j (4*r) _ _ (Geo.Reads.way hV.reads (hy.shrink (by omega)))
  have hg : AgreeNear S.ratio.parent j (4*r) (pull s 0 U) (pull s 0 U'):=pulled_near _ _ _ _ _ (fun i hi=> v.peak_record hV i h.boost.ready (hy.shift (by change separation (grantPlace S _) _≤_ at hi; omega)))
  obtain ⟨hF,hI,hL,hN⟩:=Voice.Meters.with_components T x Q Q' (pull s 0 U) (pull s 0 U') _ _ h.boost.produced j hv hg he
  rcases i with ⟨s',i|i|i|i⟩
  · have he : AgreeNear S.ratio.parent (S.ratio.parent i.1) r (pull s 0 U) (pull s 0 U'):= hg.shrink (by rw [show S.ratio.parent i.1=j from rfl,separation_self]; omega)
    obtain ⟨δ,h'⟩:= h.boost.produced.fine
    have ht:= (shortcuts x (Work.E03.parent_step S) (i,false) _ _ hr le_rfl hC he).2.2
    have ht':= (shortcuts x (Work.E03.parent_step S) (i,false) _ _ hr le_rfl h' he).2.2
    have hz := hF i rfl
    unfold T at hz; unfold workF at hz
    unfold Milk.outer; change v.things.workF (till x) (pull s 0 U) _ _ _ _ = v.things.workF (till x) (pull s 0 U') _ _ _ _
    unfold workF; exact congr_arg₂ HAdd.hAdd ht (add_left_cancel (by rw [ht'] at hz; exact hz))
  · exact hI i rfl
  · obtain ⟨h1,h2,h3⟩:=hL i rfl; exact congr_arg₂ HAdd.hAdd h1 (congr_arg₂ HAdd.hAdd h2 h3)
  exact hN i rfl
lemma as_meter (h : Chips v P W x) (i : Grain S) (g : ℝ) (he : Shields X (grantPlace S i) (64*radiusB x)) : Pulled (fun p:Pilot G S x=> coinMeter v.things x p.view p.y.1 p.tag v.chi v.arc (v.combo p g) i) X:= by
  rcases i with ⟨s,i|i|i⟩
  · exact Pulled.sum (S:=S) (X:=X) (x:=x) (E:=ℝ) (univ:Finset Bool) (fun j _=> Dyed.fares_read h (s,Sum.inl (i,j)) g he)
  · exact Dyed.fares_read h (s,Sum.inr i) g he
  exact Pulled.fetch _

def dues (v : Dyed G S) (i : Grain S) (p : Pilot G S x):= -v.source.beta*(Aff.weight* Milk.levy v.things x p.view p.y.1 p.tag v.chi v.arc v.source.p.threshold (v.combo p (coupling v.source.beta)) i)
lemma heavy (v : Dyed G S) (p : Pilot G S x) : AnalyticBridge.Annulus1AD.landed x p.key p.park p.view p.y.1 (v.combo p (coupling v.source.beta))=v.top p:=by unfold Dyed.top gazed Dyed.combo; rw [mean_endpoint]; rfl
lemma bits (h : Chips v P W x) {C : ℝ} (hC : LaneCounts v.things.up x v.source.p.threshold v.things.high C 1 S.ratio.parent) (i : Grain S) (he : Shields X (grantPlace S i) (64*radiusB x)): Pulled (dues v (x:=x) i) X:= by
  have ht:= hold_outer h hC i he
  have hz:= (ht.covers (as_meter h i (coupling v.source.beta) he)).twine (measurable_fst.sub measurable_snd)
  have hp:= hz.plus (as_meter h i 0 he)
  apply Pulled.times (v:=fun p=> Aff.weight*levy v.things x p.view p.y.1 p.tag v.chi v.arc v.source.p.threshold (v.combo p _) i) (Pulled.fetch (-v.source.beta))
  refine (Pulled.fetch _).times (hp.conforme fun p h=>?_)
  unfold levy; rw [heavy, ← mean_endpoint]; exact congr_arg₂ HAdd.hAdd rfl (by simp only [Dyed.combo,zero_smul,add_zero])
-- Use exactly 200H; occupancy density includes Co Gain stencils. Need 420H outside classification support. Scalar bounds before any posted Load markup.
def center (i : Core S x) (v : Dyed G S) (p:Pilot G S x):= ∑ j∈ceilingE i.val (200*radiusB x), dues v j p

def lapse (v : Dyed G S) (i : Grain S) (p : Pilot G S x):= if i∈ ceilingE p.key (200*radiusB x) then 0 else dues v i p
def penury (v : Dyed G S) (p:Pilot G S x):= ∑ i,lapse v i p
lemma summers (ι : Type) [Fintype ι] (o : ι→ Site c) (w : Pilot G S x) (Z : ι→ℝ) (D : ℕ) (hd : D≤500*radiusB x) :
    (∑ i,Z i)=(∑ i∈owners w.key x,∑ j∈univ.filter (fun j=> o j∈ i.val.dome D),Z j)+∑ i,if o i∈w.key.dome D then 0 else Z i:= by
  let f (A : Core S x):= univ.filter fun j=> o j∈ A.val.dome D
  let T:= univ.filter fun i=>o i∈w.key.dome D
  have hp: T=(owners w.key x).biUnion f:= by
    ext i; unfold T f; rw [← owner_dome w.key x]; simp only [mem_filter,mem_univ,true_and, mem_biUnion]
  have hj : ∑ i, (if o i∈w.key.dome D then (0:ℝ) else Z i)=∑ i∈Tᶜ,Z i:=by
    have hu:Tᶜ=univ.filter (fun i=> o i∉w.key.dome D):= by ext; simp [T]
    rw [hu,sum_filter]; apply Finset.sum_congr rfl; intro i hi; split_ifs <;> rfl
  have hl: (∑ i∈T,Z i)=∑ i∈owners w.key x,∑ j∈f i,Z j:= by
    rw [hp, Finset.sum_biUnion]; intro i hi j hh ht
    have hZ:= ((owner_eq (owners w.key x)).1 rfl).1 hi hh ht
    exact disjoint_left.mpr fun l ha hb=> disjoint_left.mp hZ (AnalyticBridge.Annulus1AD.farther hd ((mem_filter.mp ha).2)) (AnalyticBridge.Annulus1AD.farther hd ((mem_filter.mp hb).2))
  rw [hj,← hl]; exact (sum_add_sum_compl ..).symm
lemma reindex (v : Dyed G S) (p:Pilot G S x): (∑ i, dues v i p) = (∑ i∈owners p.key x,center i v p)+penury v p:= by
  rw [summers (Grain S) (grantPlace S) p (fun i=> dues v i p) (200*radiusB x) (by omega)]; unfold center penury lapse ceilingE
  exact congr_arg₂ HAdd.hAdd rfl (Finset.sum_congr rfl fun i _=> by simp only [mem_filter,mem_univ,true_and])
lemma center_read (h : Chips v P W x) {C : ℝ} (hC : LaneCounts v.things.up x v.source.p.threshold v.things.high C 1 S.ratio.parent) (i : Core S x): Pulled (center i v) (acre i):= by
  refine Pulled.sum (S:=S) (X:=acre i) (x:=x) (E:=ℝ) _ fun j hj=> bits h hC j (fun k hk=>?_)
  obtain ⟨s,hs,h⟩:=halo_spec.mp (mem_filter.mp (show _∈ceilingE .. from hj)).2; exact halo_spec.mpr ⟨s,hs,(separation_triangle s (grantPlace S j) _).trans (by omega)⟩

def pond (S : StepData c f) (x : ℝ) (i : Grain S):= halo (420*radiusB x) {grantPlace S i}
lemma lapse_read (h : Chips v P W x) {C : ℝ} (hC : LaneCounts v.things.up x v.source.p.threshold v.things.high C 1 S.ratio.parent) (i : Grain S): Pulled (lapse v (x:=x) i) (pond S x i) := by
  have ht: Shields (pond S x i) (grantPlace S i) (420*radiusB x):= covers_shield _ (mem_singleton_self _); have he:=bits h hC i (ht.shrink (by omega))
  refine ⟨fun A F k=> ?_, fun p q ha hb hp=>?_⟩
  · unfold lapse; by_cases ht : i∈ ceilingE A (200*radiusB x)
    · dsimp only; simp_rw [if_pos ht]; exact (Pulled.fetch 0 (X:=pond S x i)).enter A F k
    dsimp only; simp_rw [if_neg ht]; exact he.enter ..
  unfold lapse ceilingE; simp only [mem_filter,mem_univ,true_and]; exact if_congr ( hp.reads.dome_agrees (200*radiusB x) _ (ht.shrink (by have hB:= h.boost.produced.scale; omega))) rfl (he.agreed ha hb hp)
end YM.PhysicalNext.InteractingRank.Pump.Coffer
