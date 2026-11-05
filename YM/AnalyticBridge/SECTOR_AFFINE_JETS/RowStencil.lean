import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Ingredients
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Wisps


/-!
# Local data reads of the covariance rows

Keep x,T/path data, Stores (including costs, flags, aisles), tree, prediction
tag and colors fixed. Prove numerical dependence radii for the V variable and
fine input. When using inside the allocation one must still additionally keep
all flag/Store etc queries. These stencils are *not* support bounds on
post-integration multipliers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Lattice Wilson RG Precision Pressure Tree
open YM.Next.Fluctuations YM.Next.SectorChange YM.Next.SectorChange.Rows
open YM.Next.SectorChange.Wisps
open YM.Push.SectorMeasure.Oriented
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {P : Patch} {c f : Side} {S : StepData c f}

/-- Read-out center for a scalar V coordinate. -/
abbrev coordRoot (u : Coord G c) : Site c := u.1.1

lemma field_dep {V W : Config G c} {o : Site c} {r : ℕ}
    (h : AgreeNear id o r V W) {v w : PriceCoords G c}
    (e : ∀ i : Coord G c, separation o (coordRoot i) ≤ r → v i=w i) :
    AgreeNear id o r (field V v) (field W w) := by
  intro i hi; unfold field increment
  have hu : tape v i=tape w i := by ext j; exact e (i,j) hi
  rw [hu,h i hi]

lemma facade_dep {s : Signed} {V W : Config G c} {a b : Directions G f} {o : Site c} {r : ℕ}
    (h : AgreeNear id (s.act o) (r+1) V W) (e : echo S (s.act o) (r+1) a b) :
    AgreeNear S.ratio.parent o r (facade S s V a) (facade S s W b) := by
  apply pulled_near
  intro i hi; unfold increment; rw [e i hi]; congr 1
  unfold replica; split
  · rfl
  exact h _ hi

lemma face_field_dep {V W : Config G c} (p : Cell f) (s : Signed)
    (h : AgreeNear id (s.act (S.ratio.parent p.1)) 5 V W) :
    plaquetteJet S V s p = plaquetteJet S W s p := by
  apply congr_arg (fun (f : Directions G f → G.Color) => fderiv ℝ f 0)
  funext i; apply congr_arg G.curvature
  exact travel_near _ (YM.Work.E03.parent_step S) _ _ _ _ 4 le_rfl
    (facade_dep h (fun _ _ => rfl))

lemma predictor_field_dep {V W : Config G c} (k : S.Choices) (p : Bond c) (s : Signed)
    (hk : S.patch.Branches S.kernel G) (h : AgreeNear id (s.act p.1) (predReach S.patch+1) V W) :
    blockJet V k s p=blockJet W k s p := by
  have he (a : Directions G f) : predictGroup V k s p a = predictGroup W k s p a :=
    prediction_near_eq hk _ _ _ _ (facade_dep h (fun _ _ => rfl))
  apply congr_arg (fun (f : Directions G f → G.Color) => fderiv ℝ f 0)
  funext i; unfold predictorTurn; rw [he i,he 0]

lemma transported_field_dep {V W : Config G c} (p : Cell f) (s : Signed) (l : RG.Slot) (a : Directions G f)
    (h : AgreeNear id (s.act (S.ratio.parent p.1)) (l.length+5) V W) :
    G.adjoint (travel (facade S s V 0) p.1 l.walk)
      (plaquetteJet S V s (YM.Work.F03.slotFace l p.1) a) =
    G.adjoint (travel (facade S s W 0) p.1 l.walk)
      (plaquetteJet S W s (YM.Work.F03.slotFace l p.1) a) := by
  have ha : l.walk.length ≤ l.length := Nat.le_add_right ..
  have hl : AgreeNear S.ratio.parent (S.ratio.parent p.1) l.length (facade S s V 0) (facade S s W 0) :=
    facade_dep (h.shrink (by rw [separation_self]; omega)) (fun _ _ => rfl)
  rw [travel_near _ (YM.Work.E03.parent_step S) _ _ _ _ l.length ha hl, face_field_dep _ _ ?_]
  refine h.shrink ?_
  rw [separation_signed]
  exact Nat.add_le_add_right ((slot_distance ..).trans ha) 5

section active
variable {x : ℝ} {A : Stores S} {F : Forest S.ratio}

/-- The true single-vector input to `move`. -/
abbrev sourceKey (j : Rows.In x A F (G:=G)) : Directions G f :=
  fresh x (shots S x) A F (axisPrice j)

lemma sourceKey_eq (j : Rows.In x A F (G:=G)) :
    sourceKey j=Pi.single j.1.val.val (EuclideanSpace.basisFun G.ColorIndex ℝ j.2) := by
  funext i
  by_cases hi : i=j.1.val.val
  · subst i; unfold sourceKey; rw [Next.SectorChange.Gap.freshly_read,on_axis]; simp
  rw [Pi.single_eq_of_ne hi]; unfold sourceKey fresh; split
  · rename_i hx; split
    next hb =>
      rw [on_axis]
      apply Pi.single_eq_of_ne
      exact fun he => hi (congr_arg (fun i : Active A x F => i.val.val) he)
    rfl
  rfl

abbrev fineRay (j : Coord G f) : Directions G f :=
  Pi.single j.1 (EuclideanSpace.basisFun G.ColorIndex ℝ j.2)

abbrev location (S : StepData c f) (j : Coord G f) := S.ratio.parent j.1.1

lemma fineRay_norm (j : Coord G f) : ‖fineRay j‖ = 1 := by
  change ‖(LinearIsometry.single ℝ (fun _ : Bond f => G.Color) _) _‖ = _
  rw [LinearIsometry.norm_map,OrthonormalBasis.norm_eq_one]

lemma fine_anchored {j : Coord G f} {o : Site c} {r : ℕ} (h : ¬separation o (location S j) ≤ r) :
    echo S o r (fineRay j) 0 := by
  intro i hi
  by_cases he : i=j.1
  · subst i; exact (h hi).elim
  exact Pi.single_eq_of_ne he _

lemma off_face {j : Coord G f} {s : Signed} {p : Cell f}
    (h : ¬separation (s.act (S.ratio.parent p.1)) (location S j) ≤ 5) (V : Config G c) :
    plaquetteJet S V s p (fineRay j) = 0 := by rw [faceJet_dep V s p _ _ (fine_anchored h),map_zero]

lemma off_prediction {j : Coord G f} {k : S.Choices} {s : Signed} {p : Bond c}
    (hb : S.patch.Branches S.kernel G)
    (h : ¬separation (s.act p.1) (location S j) ≤ predReach S.patch+1) (V : Config G c) :
    blockJet V k s p (fineRay j)=0 := by rw [blockJet_dep V k s p _ _ hb (fine_anchored h),map_zero]

lemma off_piece {l : RG.Slot} {V : Config G c} {o : Cell f} {j : Coord G f} {s : Signed}
    (h : ¬separation (s.act (S.ratio.parent o.1)) (location S j) ≤ l.length+5) :
    piece S V s (fineRay j) o l=0 := by
  funext y
  unfold piece
  rw [off_face (S:=S) _ _,map_zero]; swap
  · contrapose! h
    set p := YM.Work.F03.slotFace l o.1
    apply (separation_triangle _ (s.act (S.ratio.parent p.1)) _).trans
    rw [separation_signed]; refine Nat.add_le_add ?_ h
    exact (slot_distance ..).trans (Nat.le_add_right ..)
  rfl

lemma anchored {j : Rows.In x A F (G:=G)} {o : Site c} {r : ℕ} (h : ¬separation o (front A F j) ≤ r) :
    echo S o r (sourceKey j) 0 := by
  rw [sourceKey_eq]
  exact fine_anchored (j:=(j.1.val.val,j.2)) h

lemma no_dispatch (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices)
    (i : Receipt G S) (j : Rows.In x A F (G:=G)) (h : S.patch.Branches S.kernel G)
    (he : ¬separation (Wisps.down S i) (Wisps.front A F j) ≤ span S.patch x) (V : Config G c) :
    move T x V k (shots S x) A F i j=0 := by
  rcases i with ⟨⟨s,u⟩,b⟩
  change Rows.restrict _ _ _ _ (bump T x V k (sourceKey j)) (s,u) b = 0
  unfold Rows.restrict; split
  · rw [bump_dep T x V k s u _ 0 h ?_]
    · have ht : bump T x V k 0 (s,u)=0 := by cases u <;> simp [bump,faceKick,noiseKick,barrel]
      simp [ht]
    intro e he'
    exact anchored he e ((contains ..).mp he')
  rfl




end active
end YM.AnalyticBridge.SectorAffine
