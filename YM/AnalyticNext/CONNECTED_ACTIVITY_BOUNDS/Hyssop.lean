import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Strews

/-!
# Pricing neighborhoods for all predictor reads

Prove for both amplitudes AND Pt tag likelihoods; keep extra label footprints.
Reproduce a few private arguments of Prediction needed locally now for branch switches (with actual tag variation).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Coverage
open Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores MeasureTheory Push.SectorMeasure
open Matrix Push.SectorMeasure.Oriented Push.AbsoluteSums Tree Next.Fluctuations Filter Win Win.Promise Finset
open Centered Aff Aff.Mint Wages Jewels   Mixed Work.E03
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

section P

variable (P : Patch)

def flight (x y : P.Points) (l : Lattice.Order) := (visits x.val (route x.val y.val l)).toFinset
def hikeB (i : Axis) (x : P.Points) := (visits x.val (List.replicate P.L.val (posDir i))).toFinset

def beds := P.sites ∪ ((univ : Finset P.Points).biUnion fun x =>
    (univ.biUnion fun y : P.Points => univ.biUnion fun l : Lattice.Order => flight P x y l) ∪
      univ.biUnion fun i : Axis => hikeB P i x)

def shutters := (beds P).sup (fun x => (route 0 x 1).length)

lemma exp_patch (S : StepData c f) (x : Site c) (U U' : Config G f)
    (h : AgreeNear S.ratio.parent x (shutters S.patch) U U') (i : Edge Cover) (hi : i.1 ∈ beds S.patch) :
    expandAt (S.ratio.embed x) U i=expandAt (S.ratio.embed x) U' i := by
  unfold expandAt; apply h
  let q := S.ratio.embed x; let w := route 0 i.1 1
  have hy := Work.E03.sep_walk _ (Work.E03.parent_step S) q w
  rw [show stop q w=wrap f i.1+q from by simpa only [map_zero,add_zero,add_comm] using stop_route q 0 i.1,
    show S.ratio.parent q=x from S.ratio.embed_parent _] at hy
  exact hy.trans (Finset.le_sup (f:=fun x => (route 0 x 1).length) hi)

lemma flight_patch (K : KernelChoices) (hb : P.Branches K G) (U V : CoverConfig G)
    (h : ∀ i : Edge Cover,i.1∈ beds P → U i=V i) : ∀ t : P.FrameTag,P.frame K U t=P.frame K V t ∧
      P.frameMass K U t=P.frameMass K V t := by
  intro t
  have hr x y l : travel U (x:P.Points).val (route x.val (y:P.Points).val l) = travel V x.val (route x.val y.val l) := by
    apply travel_local _ _ U V
    exact fun i hi _ => h i (mem_union_right _ (mem_biUnion.mpr ⟨x,mem_univ x,mem_union_left _ <|
      mem_biUnion.mpr ⟨y,mem_univ y,mem_biUnion.mpr ⟨l,mem_univ l,List.mem_toFinset.mpr hi⟩⟩⟩))
  have he (x : P.FrameTag) : P.axial U x=P.axial V x := funext (fun i => hr x.1 i x.2)
  have hf (f : P.Frame G) : P.via f U=P.via f V := funext (fun x => funext fun y => funext fun l => by rw [via,via,hr x y l])
  have hy : P.usesMin K U ↔ P.usesMin K V := by simp only [usesMin,he,hf]
  have hV : P.score U=P.score V := by funext f; simp only [score,hf]
  by_cases hk : P.usesMin K V
  · refine ⟨?_,by simp only [frameMass,hk, hy.mpr hk, if_true]⟩
    have hp : P.minimizing V (P.selected U) := by
      simp only [minimizing,← hV]; exact (P.min_exists U).choose_spec
    simp only [Patch.frame,hy.mpr hk,hk,if_true]; exact (hb.frame_unique V hk).unique hp (P.min_exists V).choose_spec
  constructor
  · simp only [Patch.frame,if_neg hk,if_neg (mt hy.mp hk),he]
  have hg : P.facesum U=P.facesum V := by
    unfold facesum; refine sum_congr rfl fun i _ => sum_congr rfl fun p _ => ?_
    split
    next hq =>
      apply congr_arg G.chord
      apply travel_local _ _ U V
      intro j hx hh; exact h j (mem_union_left _ (hq _ hx))
    rfl
  have hA i : P.axialCost U i=P.axialCost V i := by
    unfold Patch.axialCost; apply sum_congr rfl; intro v _
    exact sum_congr rfl fun j _ => by
      split
      · rw [he, h (v.val,j) (mem_union_left _ v.property)]
      rfl
  have hp : P.eligible K U=P.eligible K V := by simp only [eligible,hA,hg]
  unfold frameMass; simp [hy,hk,hp]

lemma connector_at (U U' : Config G f) (k k' : S.Choices) (i : Bond c)
    (hb : S.patch.Branches S.kernel G) (he : AgreeNear S.ratio.parent i.1 (shutters S.patch+1) U U')
    (hh : k.1 i.1=k'.1 i.1) (hq : k.1 (i.1+step i.2)=k'.1 (i.1+step i.2)) (hp : k.2 i=k'.2 i) :
    αSite U i.1 k=αSite U' i.1 k' ∧ αBond U i k=αBond U' i k' ∧ S.prediction U k i=S.prediction U' k' i := by
  let y := i.1+step i.2
  have hw j := exp_patch S i.1 U U' (he.shrink (by rw [separation_self]; omega)) j
  have hx := flight_patch S.patch S.kernel hb _ _ hw
  have ht j := flight_patch S.patch S.kernel hb _ _ (exp_patch S y U U' (he.shrink
    ((Nat.add_le_add_right (Work.E03.sep_step ..) _).trans (by omega)))) j
  have hy : S.connector U k.1 i=S.connector U' k'.1 i := by
    funext p
    unfold StepData.connector StepData.frames
    rw [hh,hq, (hx _).1, (ht _).1]
    congr 2
    apply travel_local _ _ (expandAt (S.ratio.embed i.1) U) (expandAt (S.ratio.embed i.1) U')
    intro j hi hT
    exact hw j (mem_union_right _ (mem_biUnion.mpr ⟨p,mem_univ p,mem_union_right _ <|
      mem_biUnion.mpr ⟨i.2,mem_univ _,List.mem_toFinset.mpr hi⟩⟩))
  exact ⟨by unfold αSite; rw [hh,(hx _).2],by unfold αBond; rw [hp,hy], by unfold StepData.prediction; rw [hp,hy]⟩
end P

-- radius budget & lane. generated eventually via Service
structure Optic (T : Tube G S) (x : ℝ) (C : ℝ) : Prop where
  giant : 100≤radiusB x
  meeting : 16*(2*till x+Next.Fluctuations.predReach S.patch+shutters S.patch+10) ≤ radiusB x
  up : Bid.LaneCounts T.up x (fiery G x S.patch.L) T.high C 1 S.ratio.parent
  down : Bid.LaneCounts T.down x (temp x) T.low C S.patch.L.val (id : Site c→Site c)



namespace Shed
variable {T : Tube G S} {A A' : Stores S} {X : Support c} {F : Forest S.ratio} {x : ℝ}
  {Y : Mint T F A x} {Y' : Mint T F A' x} (h : Shed F Y Y' X)
  {P : Teller G} (hT : P.Funds S T) {U W : Config G f}
include h hT




end Shed
end YM.AnalyticNext.ConnectedActivity.Coverage
