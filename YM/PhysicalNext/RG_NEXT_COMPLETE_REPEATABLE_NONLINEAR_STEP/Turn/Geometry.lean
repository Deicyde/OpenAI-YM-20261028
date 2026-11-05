import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Zest
import YM.PhysicalNext.ORDERED_AFFINE_2B.CompactResolvent
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymRows
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Bass


/-! # Physical geometry of pull of the E6 spelling

Call one `(s,b)` for coarse, in fine pull by WHOLE `(s,g.embed b)`. In pair
and log labels, seats always refer to *channel* positions and must be
readdressed by `(s*q,d)`, not just turning around q's anchor. This handles
the physical period even when every halo wraps fully.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Set Finset Lattice Wilson RG Pressure Tree
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows
open Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {F : Forest S.ratio} (s : Signed) (b : Site c)

def books (S : StepData c f) : Equiv.Perm (Stores S) where
  toFun A := Locations.book s b A
  invFun A := ⟨A.costs.map (Locations.shiftFaces s (S.ratio.embed b)).toEmbedding, A.aisles.map (StepData.sendBonds s b).toEmbedding,A.flags.map (StepData.sendSites s b).toEmbedding⟩
  left_inv A := by rcases A with ⟨a,x,v⟩; dsimp only [Locations.book]; congr <;> ext <;> simp
  right_inv A := by rcases A with ⟨a,x,v⟩; dsimp only [Locations.book]; congr <;> ext <;> simp

section maps
variable {α β γ δ : Type} (e : α≃β)
lemma given [DecidableEq α] [DecidableEq β] (x : Finset α) (y : Finset β) :
    y=x.map e.toEmbedding ↔ ∀ i,i∈x ↔ e i∈y := by
  constructor
  · rintro rfl i; simp
  intro h; ext i; obtain ⟨i,rfl⟩ := e.surjective i; rw [← h i]; simp
lemma display [DecidableEq α] [DecidableEq β] (x : Finset α) (y : Finset β) :
    y=x.image e ↔ ∀ i,i∈x ↔ e i∈y := (iff_of_eq (by rw [← given e x y, map_eq_image]; rfl))
lemma assign_guard [DecidableEq α] [DecidableEq β] {x y : Finset α} {x' y' : Finset β}
    (h : ∀ i,i∈x ↔ e i∈x') (hh : ∀ i,i∈y ↔ e i∈y') : Disjoint x y ↔ Disjoint x' y' := by
  rw [(given e x x').mpr h, (given e y y').mpr hh]; simp
lemma values {K : Type*} [CommMonoid K] [DecidableEq α] [DecidableEq β] (x : Finset α) (y : Finset β)
    (h : ∀ i, i∈x ↔ e i∈y) (f : α→K) (g : β→K) (he : ∀ i,i∈x → f i=g (e i)) : ∏ i∈x,f i=∏ i∈y,g i := by
  rw [(given e x y).2 h, Finset.prod_map]; exact prod_congr rfl he
lemma bills [DecidableEq α] [DecidableEq β] (x : Finset α) (y : Finset β)
    (h : ∀ i, i∈x ↔ e i∈y) (f : α→ℝ) (g : β→ℝ) (he : ∀ i,i∈x → f i=g (e i)) : ∑ i∈x,f i=∑ i∈y,g i := by
  rw [(given e x y).2 h, Finset.sum_map]; exact sum_congr rfl he
end maps

lemma halo_pull (n : ℕ) (x : Support c) (y : Support c) (he : ∀ i,i∈x ↔ affine s b i∈y) :
    halo n y=(halo n x).image (affine s b) := by
  apply (display (StepData.sendSites s b) ..).2; intro i
  rw [halo_spec,halo_spec]
  conv_rhs => rw [← (StepData.sendSites s b).exists_congr_right]
  change _ ↔ ∃ j,affine s b j∈y ∧ separation (affine s b j) (affine s b i) ≤ n
  simp_rw [← he, affine,separation_translate,separation_signed]
lemma surround (A : Stores S) (n : ℕ) : A.dome n=((Locations.book s b A).dome n).image (affine s b) :=
  halo_pull s b n _ _ (Locations.place_map s b A)
lemma ends_full (i : Bond f) : Shell.ends S (diagram s b S i) = (Shell.ends S i).image (affine s b) := by
  change Shell.ends S (sendEdge s _ i)=_
  unfold Shell.ends; rw [Locations.pin_map, Finset.image_image,Finset.image_image]; congr 1; exact funext (fun x=> Locations.parent_map s b x)
lemma pointers (i : Bond c) : pinPos (StepData.sendBonds s b i)=(pinPos i).image (affine s b) := Locations.pin_map s b i
lemma walk_near (x y : Site c) : separation (affine s b x) (affine s b y)=separation x y := by simp [affine]
lemma remains_hot (A : Stores S) (F : Forest S.ratio) (w : ℕ) (i : Bond f) : Shell.active (Locations.forest s b F) (Locations.book s b A) w i ↔ Shell.active F A w (diagram s b S i) := by
  have he := assign_guard (x:=(Locations.book s b A).dome (10*w)) (y:=Shell.ends S i) (StepData.sendSites s b) (Locations.dome_map s b A (10*w)) ((display _ _ _).1 (ends_full s b i))
  refine and_congr (not_congr (Locations.trunk_map ..)) (not_congr (not_congr he))

lemma travels (A : Stores S) (n : ℕ) (i : Bond f) : voyage (Locations.book s b A) n i ↔ voyage A n (diagram s b S i) := by
  unfold voyage; refine not_congr (assign_guard (StepData.sendSites s b) (Locations.dome_map s b A n) ((display _ _ _).1 (ends_full ..)))

-- Channel: q on the pulled field evaluates (s*q) on the original translated
-- patch. Even for N-row, keep the label. shifts forward old. Appropriate level
-- size (site c vs f) explicitly induced by S.
def wind (S : StepData c f) (q : Signed) : Equiv.Perm (Spot c f) :=
  let v := offset s b q
  Equiv.sumCongr (Channels.shift (S.ratio.embed v) _) <| Equiv.sumCongr (Channels.shift v _) <|
      Equiv.sumCongr (Channels.shift v _) (Channels.shift v _)
def whirl (S : StepData c f) : Equiv.Perm (Stream c f) where
  toFun i := (s*i.1,wind s b S i.1 i.2)
  invFun i := (s⁻¹*i.1,(wind s b S (s⁻¹*i.1)).symm i.2)
  left_inv i := by simp
  right_inv i := by simp
lemma partner (i : Spot c f) (q : Signed) : lead S (wind s b S q i)=lead S i+offset s b q := by
  rcases i with i|i|i|i
  · simpa only [affine,Signed.act_one] using! Locations.parent_map (S:=S) 1 (offset s b q) i.1
  all_goals rfl
lemma center_meets (i : Stream c f) : rowSite S (whirl s b S i)=affine s b (rowSite S i) := by
  rcases i with ⟨q,i⟩
  change (s*q).act (lead S (wind s b S q i))=_
  rw [partner, Signed.act_add,Channels.offset,Signed.act_inv]; change _ + b=affine s b (q.act (lead S i))
  rw [Signed.act_mul]; rfl
lemma posted_roll (A : Stores S) (q : Signed) (i : Spot c f) (n : ℕ) :
    i∈posted (turnStore q (Locations.book s b A)) n ↔ wind s b S q i ∈ posted (turnStore (s*q) A) n := by
  simp only [posted,mem_filter,Finset.mem_univ,true_and, Shell.Inside,Channel.rotates_dome,Locations.dome_map]
  change affine s b _∈A.dome n ↔ rowSite S (whirl s b S (q,i)) ∈ A.dome n; rw [center_meets]; rfl
lemma rod_honors (i : Rod c f) (q : Signed) : spot S (shiftSlot s b q S.ratio i) = wind s b S q (spot S i) := by cases i <;> rfl
lemma parents_go (i : Spot c f) (q : Signed) (j : Rod c f) :
    j∈parents i ↔ shiftSlot s b q S.ratio j∈parents (wind s b S q i) := by
  rw [parent_iff (S:=S),parent_iff (S:=S),rod_honors]; exact (wind s b S q).injective.eq_iff.symm

lemma label_selection {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)} (hx : Y.x=X.x) (hA : Y.seeds=Locations.book s b X.seeds)
    (j : Mention c f) : Y.selected j.1 (spot S j.2) ↔ X.selected (perChannel s b S j).1 (spot S (perChannel s b S j).2) := by
  obtain ⟨q,j⟩:=j
  have he := center_meets (S:=S) s b (q,spot S j)
  change ¬Inside (rowSite S (q,spot S j)) Y.seeds (6*Y.B) ↔ ¬ Inside (rowSite S (s*q,spot S (shiftSlot s b q S.ratio j))) X.seeds (6*X.B)
  unfold Coat.B Shell.Inside; rw [hx,hA, Locations.dome_map,← he,rod_honors]; rfl
end YM.PhysicalNext.Repeat.Turn
