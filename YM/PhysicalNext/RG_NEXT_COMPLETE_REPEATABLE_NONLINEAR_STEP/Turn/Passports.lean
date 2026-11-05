import YM.Further.THRESHOLD_SOURCE_RESTART.Spin
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Motion


/-! # Supports of entire optional alphabet, not conditional on value. Keeps
all previous read-halos. `transStory` not recomputing blob sizes etc when
path charges later included. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (s : Signed) (b : Site c)

-- channel offset reanchor independent of level.
def leave {α : Type*} (p : Signed→Equiv.Perm α) : Equiv.Perm (Signed × α) where
  toFun i := (s*i.1,p i.1 i.2)
  invFun i := (s⁻¹*i.1,(p (s⁻¹*i.1)).symm i.2)
  left_inv i := by simp
  right_inv i := by simp

def rotateMini (S : StepData c f) : Equiv.Perm (Miniature c f) := Equiv.sumCongr (whirl s b S)
    (Equiv.sumCongr (diagram s b S) (diagram s b S))
lemma town_turn (i : Bond f) (B l : ℕ) : town S B l (diagram s b S i)=(town S B l i).image (affine s b) :=
    halo_pull s b _ _ _ ((display (StepData.sendSites s b) ..).1 (ends_full ..))
lemma circle_wind (x : Site c) (B : ℕ) : Animals.neighbors B (affine s b x)=(Animals.neighbors B x).image (affine s b) := by
  apply (display (StepData.sendSites s b) ..).2; intro i; rw [Animals.neighbors_mem,Animals.neighbors_mem]; change _ ↔ separation _ (affine s b i)≤ B; rw [show separation _ _=_ from walk_near s b x i]
lemma sleeve_turn (i : Miniature c f) (B l : ℕ) : sleeve S B l (rotateMini s b S i)=(sleeve S B l i).image (affine s b) := by
  rcases i with i|i|i
  · change Animals.neighbors _ (rowSite S (whirl s b S i)) = _; rw [center_meets]; exact circle_wind ..
  · exact town_turn ..
  exact town_turn ..
lemma visit_turn (j : Bond f) {n : ℕ} (i : Itinerary f n) (B l : ℕ) : visited S B l (diagram s b S j) (sequence (diagram s b S) _ i)= (visited S B l j i).image (affine s b) := by
  induction n generalizing j with
  | zero=> rw [visited,visited,town_turn]
  | succ n ih=> rw [visited,visited,town_turn,image_union]; exact congr_arg _ (ih (Itinerary.next i) (Itinerary.after i))
lemma via_turn {n : ℕ} (B l : ℕ) (i : Ledger f n) : receipt S B l n (portage s b S n i)= (receipt S B l n i).image (affine s b) := visit_turn ..
lemma kindle_turn (B l : ℕ) (i : ChainIndex f) : basisFoot S B l (rotationFuel s b S i)=(basisFoot S B l i).image (affine s b) := by
  rcases i with i|i|i|i|i
  · exact via_turn ..
  · exact via_turn ..
  · exact via_turn ..
  · exact town_turn ..
  exact via_turn ..

def sky : Equiv.Perm (Trans c) := leave s fun q => Channels.shift (offset s b q) _
def moon : Equiv.Perm (Pairs c) := leave s fun q => Equiv.prodCongr (Equiv.refl _) (Channels.shift (offset s b q) _)
def rotateStory (S : StepData c f) (π : Equiv.Perm ℕ) : Equiv.Perm (LogLetter c f) :=
    let y:=sky s (S.ratio.embed b)
    Equiv.sumCongr π (Equiv.sumCongr y (Equiv.sumCongr y (Equiv.sumCongr y (Equiv.sumCongr (moon s (S.ratio.embed b)) (moon s b)))))

lemma merger (Z X : Support f) (he : ∀ i, i∈Z ↔ affine s (S.ratio.embed b) i ∈ X) : X.image S.ratio.parent=(Z.image S.ratio.parent).image (affine s b) := by
  let p:=StepData.sendSites s (S.ratio.embed b)
  rw [(display p Z X).2 he,image_image,image_image]; congr 1; exact funext fun x=> Locations.parent_map ..
lemma pathFo (K L : Finset Cover) (h : K=L) (x : Site c) : L.image (fun p => Lattice.wrap c p+(x+b))=(K.image fun p => Lattice.wrap c p+x).image (affine 1 b) := by subst L; rw [image_image]; congr 1; funext j; simp only [Function.comp_apply]; simp only [affine,Signed.act_one,add_assoc]
lemma mateFo (p : PathData G) (x : Cell c) (B : ℕ) (i : ℕ×ℕ) : pairFoot B p (Channels.shift b _ x) i = (pairFoot B p x i).image (affine 1 b) := by
  unfold pairFoot; rw [image_union]; apply congr_arg₂
  · apply halo_pull; intro i
    change i∈{x.1} ↔ affine 1 b i ∈ ( {x.1+b} : Support c)
    simp [affine]
  unfold Paths.bundle
  rw [Finset.image_insert,Finset.biUnion_image]; apply congr_arg₂ insert (by simp [Channels.shift,affine]); congr 1; funext j
  exact pathFo b _ _ rfl x.1
lemma enlarge_shift (g : Ratio c f) (B l : ℕ) (Z X : Support f) (h : X=Z.image (affine 1 (g.embed b)))
    (he : ∀ i : Site f,g.parent (affine 1 (g.embed b) i)=affine 1 b (g.parent i)) : Footprint.enlargement g B l X=(Footprint.enlargement g B l Z).image (affine 1 b) := by
  apply halo_pull; apply (display (StepData.sendSites 1 b) (image _ Z) (image _ X)).1; subst X; rw [image_image,image_image]; apply Finset.image_congr; intro i hi; exact he i
lemma orient_shift (q : Signed) (X Y : Support c) (he : X=Y.image (affine 1 (offset s b q))) :
    X.image (affine (s*q) 0)=(Y.image (affine q 0)).image (affine s b) := by
  rw [he,image_image,image_image]; congr 1; funext i; change affine _ _ (affine _ _ i)=_
  simp only [Function.comp_apply,affine,Signed.act_one,Signed.act_add,offset,Signed.act_inv,add_zero,Signed.act_mul]
lemma footprints (L : Site c) {n} (A : Atom G n) : inspected (A.footprint (L+b))=(inspected (A.footprint L)).image (affine 1 b) := by
  rw [← Further.ThresholdSourceRestart.Sluice.Menu.looks]; apply congr_arg; exact pathFo b _ _ rfl L

lemma canonic {d : ℕ} (A : ℕ→Atom G d) (R l : ℕ) (i : Trans f) :
    atomFoot S.ratio R l A (sky s (S.ratio.embed b) i)=(atomFoot S.ratio R l A i).image (affine s b) := by
  rcases i with ⟨q,x,p⟩; apply orient_shift
  unfold sky leave at *
  change Footprint.enlargement S.ratio R l (inspected ((A p).footprint (x+offset s (S.ratio.embed b) q)))=_; rw [offset_fine]
  exact enlarge_shift (offset s b q) S.ratio _ _ _ _ (footprints ..) (Locations.parent_map 1 (offset s b q))
lemma pairs_input (p : PathData G) (R l : ℕ) (i : Pairs f) :
    bothFoot S.ratio R l p (moon s (S.ratio.embed b) i) = (bothFoot S.ratio R l p i).image (affine s b) := by
  rcases i with ⟨q,y,x,i,j⟩; apply orient_shift
  change Footprint.enlargement S.ratio R l (pairFoot l p (x+offset s (S.ratio.embed b) q,y) (i,j))=_; rw [offset_fine]
  exact enlarge_shift (offset s b q) S.ratio _ _ _ _ (mateFo (S.ratio.embed _) p (x,y) l _) (Locations.parent_map 1 (offset s b q))
lemma pairs_output (p : PathData G) (R l : ℕ) (i : Pairs c) :
    bothFoot (atOne c) R l p (moon s b i) = (bothFoot (atOne c) R l p i).image (affine s b) := by
  rcases i with ⟨q,y,x,i,j⟩; apply orient_shift
  refine enlarge_shift (offset s b q) (atOne c) _ _ _ _ ?_ (fun x=> ?_)
  · have h (i : Site c) : (atOne c).embed i=i := by simp [atOne,scaleOne,Ratio.embed]
    rw [h]; exact mateFo (offset s b q) p (x,y) l (i,j)
  have h (i : Site c) : (atOne c).embed i=i := by simp [atOne,scaleOne,Ratio.embed]
  rw [h,parent_one,parent_one]

lemma enlarged (x y : Support f) (R l : ℕ) (h : y=x.image (affine s (S.ratio.embed b))) :
    Footprint.enlargement S.ratio R l (inspected y)=(Footprint.enlargement S.ratio R l (inspected x)).image (affine s b) := by
  have he : inspected y=(inspected x).image (affine s (S.ratio.embed b)) := by rw [h,Further.ThresholdSourceRestart.Sluice.Menu.looks]
  exact halo_pull _ _ _ _ _ ((display (StepData.sendSites s b) ..).1 (merger s b _ _ ((display (StepData.sendSites s (S.ratio.embed b)) _ _).1 he)))
lemma space_roll (T : Tube G S) (R : Rep G f) (m : R.activities.Moves s (S.ratio.embed b)) (l B : ℕ) (i : LogLetter c f) :
    space T l B R (rotateStory s b S m.ep i) = (space T l B R i).image (affine s b) := by
  rcases i with i|i|i|i|i|i
  · exact enlarged _ _ _ _ _ _ (m.reg_support i)
  · exact canonic ..
  · exact canonic ..
  · exact canonic ..
  · exact pairs_input ..
  exact pairs_output ..
end YM.PhysicalNext.Repeat.Turn
