import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.District

/-!
# Physical supports of actual tags

Frames and masses even off minimizing branch. Use same `predReach`
as prior; witnesses cost envelope. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Emblems
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ μ C : ℝ} {L : Side}

private def rings (P : Patch) := univ.biUnion fun x : P.Points => univ.biUnion
  fun y : P.Points => univ.biUnion fun l : Lattice.Order => (visits x.val (route x.val y.val l)).toFinset
private def rim (P : Patch) (o : Axis) := (rings P ∪ (rings P).image (· + centerRoot P (step o))) ∪
  univ.biUnion (fun x : P.Points => (visits x.val (List.replicate P.L.val (posDir o))).toFinset)

private lemma make_ring {P : Patch} (i j : P.Points) (l : Lattice.Order) (p : Cover) (h : p∈visits i.val (route i.val j.val l)) :
    p∈rings P := mem_biUnion.mpr ⟨i,mem_univ i,mem_biUnion.mpr ⟨j,mem_univ _,mem_biUnion.mpr ⟨l,mem_univ _,List.mem_toFinset.mpr h⟩⟩⟩
private lemma inclusion (P : Patch) : P.sites⊆rings P := by
  intro x h; apply make_ring ⟨x,h⟩ P.center 1; change x∈visits x (route x _ 1)
  generalize route x _ 1=l; cases l <;> simp [Lattice.visits]

private lemma passport {P : Patch} (C : KernelChoices) (U X : CoverConfig G) (w : P.FrameTag)
    (hp : P.Branches C G) (h : ∀ b : Edge Cover, b.1∈rings P → U b=X b) :
    P.frame C U w=P.frame C X w ∧ P.frameMass C U w=P.frameMass C X w := by
  have he (x y : P.Points) (l : Lattice.Order) : travel U x.val (route x.val y.val l)=travel X x.val (route x.val y.val l) :=
    travel_local _ _ U X fun i hi _=> h i (make_ring x y l i.1 hi)
  have ha (x : P.FrameTag) : P.axial U x=P.axial X x := funext fun i=> he x.1 i x.2
  have hv (f : P.Frame G) : P.via f U=P.via f X := by funext x y l; unfold via; rw [he]
  have hs : P.score U=P.score X := by funext r; simp only [score,hv]
  have hm : P.usesMin C U ↔ P.usesMin C X := by simp only [usesMin,hv,ha]
  have hx : P.facesum U=P.facesum X := by
    unfold facesum; refine sum_congr rfl fun i _=> ?_
    refine sum_congr rfl fun j _=> ?_; split
    next hk =>
      apply congr_arg G.chord; exact travel_local _ _ U X fun a ha _=> h a <| inclusion P (hk _ ha)
    rfl
  have hl (t : P.FrameTag) : P.axialCost U t=P.axialCost X t := by
    unfold axialCost; refine sum_congr rfl fun i _=> ?_
    refine sum_congr rfl fun j _=> ?_; split
    next hy => rw [ha,h (i.val,j) (inclusion P i.2)]
    rfl
  have hj : P.eligible C U=P.eligible C X := by ext i; simp only [eligible,hx,hl]
  unfold Patch.frame frameMass; by_cases H : P.usesMin C U
  · simp only [if_pos H,if_pos (hm.mp H)]
    have h' : P.minimizing X (P.selected U) := by
      simp only [minimizing, ← hs]
      exact (P.min_exists U).choose_spec
    exact ⟨(hp.frame_unique X (hm.mp H)).unique h' (P.min_exists X).choose_spec,True.intro⟩
  rw [if_neg H,if_neg H,if_neg (hm.not.mp H),if_neg (hm.not.mp H),hj,ha]; exact ⟨rfl,rfl⟩

private lemma mime (U U' : Config G f) (q : Site c) (h : AgreeNear S.ratio.parent q (predReach S.patch) U U')
    (a : Axis) (i : Edge Cover) (hp : i.1∈rim S.patch a) :
    expandAt (S.ratio.embed q) U i=expandAt (S.ratio.embed q) U' i := by
  let w:= route 0 i.1 1; let s := S.ratio.embed q
  have hh : stop s w = wrap f i.1+s := by simpa only [map_zero, add_zero, add_comm] using Work.E03.stop_route s 0 i.1
  apply h (wrap f i.1+s,_)
  have hv := sep_walk _ (parent_step S) s w
  rw [hh, show S.ratio.parent s=q from S.ratio.embed_parent q] at hv
  apply hv.trans; change _ ≤ univ.sup (fun i : Axis => (rim S.patch i).sup _)
  exact le_trans (le_sup (f:=fun x=> (route 0 x 1).length) hp)
    (le_sup (f:=fun i:Axis=> (rim S.patch i).sup (fun x=> (route 0 x 1).length)) (mem_univ a))

variable (U U' : Config G f) (x : Site c) (i : Bond c)
variable (k k' : S.Choices)
lemma frames_agree (hb : S.patch.Branches S.kernel G) (ht : k.1 x=k'.1 x)
    (he : AgreeNear S.ratio.parent x (predReach S.patch) U U') :
    S.frames U k.1 x=S.frames U' k'.1 x ∧ Tags.siteMass U k x=Tags.siteMass U' k' x := by
  obtain ⟨hu,hv⟩ := passport S.kernel _ _ (k'.1 x) hb fun i hi => mime U U' x he 0 i
    (mem_union_left _ (mem_union_left _ hi))
  unfold StepData.frames Tags.siteMass; rw [ht,hu,hv]; exact ⟨rfl,rfl⟩

lemma choices (hb : S.patch.Branches S.kernel G) (h : k.1 i.1=k'.1 i.1)
    (hk : k.1 (i.1+step i.2)=k'.1 (i.1+step i.2)) (hz : k.2 i=k'.2 i)
    (he : AgreeNear S.ratio.parent i.1 (predReach S.patch+1) U U') :
    S.connector U k.1 i=S.connector U' k'.1 i ∧ Tags.pinMass U k i=Tags.pinMass U' k' i ∧
      S.prediction U k i=S.prediction U' k' i := by
  have hp := he.shrink (q':=i.1) (D':=predReach S.patch) (by simp)
  have hh := (frames_agree U U' i.1 k k' hb h hp).1
  have hg := (frames_agree U U' (i.1+step i.2) k k' hb hk (he.shrink (by have h:= sep_step i.1 i.2; omega))).1
  suffices hv : S.connector U k.1 i=S.connector U' k'.1 i by
    unfold Tags.pinMass StepData.prediction; rw [hv,hz]; exact ⟨rfl,rfl,rfl⟩
  funext y; dsimp only [StepData.connector]; rw [hh,hg]
  have ht := fun j (hi : j.1 ∈ visits y.val (List.replicate S.patch.L.val (posDir i.2))) => mime U U' i.1 hp i.2 j
    (mem_union_right _ (mem_biUnion.mpr ⟨y,mem_univ _,List.mem_toFinset.mpr hi⟩))
  have hx := travel_local _ _ _ (expandAt (S.ratio.embed i.1) U') (fun j hi _ => ht j hi)
  dsimp only at hx; rw [hx]
end YM.ConnectedActivityE6.Emblems
