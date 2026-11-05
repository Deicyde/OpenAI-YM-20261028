import YM.Branch.Pick

/-! Rotation of full orientation channel and cost on patches. -/

set_option autoImplicit false
noncomputable section
namespace YM.Axial
open Function Lattice Wilson Finset
open scoped Matrix.Norms.Frobenius BigOperators

/-- covariantly identified support in oriented channel. -/
lemma visits_aff (s : Signed) (t x : Cover) (w : Walk) :
    (visits x w).map (affine s t) = visits (affine s t x) (w.map (·.rotate s)) := by
  induction w generalizing x with
  | nil => simp [visits]
  | cons d w ih =>
    simp only [visits,List.map_cons,ih,Step.vec_rotate]
    rw [show affine s t (x+d.vec)=affine s t x+s.act d.vec by simp [affine, Signed.act_add]; abel]

lemma corners (x : Cover) (a b : Step) : (visits x (oriented a b)).toFinset =
    {x,x+a.vec,x+b.vec,x+a.vec+b.vec} := by
  simp only [visits, oriented,Step.vec_rev,show x+a.vec+b.vec+-a.vec = x+b.vec by abel,add_neg_cancel_right]
  ext; simp only [mem_insert,mem_singleton,List.mem_toFinset,List.mem_cons,List.not_mem_nil]; tauto

lemma all_positive (x : Cover) (a b : Step) : (visits x (oriented a b)).toFinset =
    (visits (atFace x a b) (square a.dir b.dir)).toFinset := by
  rw [corners]
  change _=(visits _ (oriented (posDir a.dir) (posDir b.dir))).toFinset
  rw [corners]; ext y
  simp only [mem_insert,mem_singleton]
  unfold atFace
  cases ha : a.neg <;> cases hb : b.neg <;>
    simp only [Step.vec, posDir, ha,hb,Bool.false_eq_true,↓reduceIte] <;>
    abel_nf <;> tauto

lemma footprint (x : Cover) (p : PlaqAxes) (s : Signed) (X : Finset Cover) (hX : X.image s.act=X) :
    (∀ i ∈ visits x (square p.val.1 p.val.2), i∈X) ↔
      (∀ i ∈ visits (Face.lower (x,p) s 0) (square (p.rotate s).val.1 (p.rotate s).val.2), i∈X) := by
  let a := p.val.1
  let b := p.val.2
  have hh (i : Cover) : affine s 0 i ∈ X ↔ i ∈ X := by
    conv_lhs => lhs; rw [← hX]
    simp only [affine,add_zero]
    simp [s.act_injective.eq_iff]
  let u := (posDir a).rotate s
  let v := (posDir b).rotate s
  let w := oriented (posDir a) (posDir b)
  have he : (visits (affine s 0 x) (oriented u v)).toFinset =
      (visits (Face.lower (x,p) s 0) (square (p.rotate s).val.1 (p.rotate s).val.2)).toFinset := by
    rw [all_positive]
    rcases lt_or_gt_of_ne (show s.perm a ≠ s.perm b from s.perm.injective.ne p.property.ne) with h|h
    · change (visits _ (square (s.perm a) (s.perm b))).toFinset = (visits _ (square (min _ _) (max _ _))).toFinset
      rw [min_eq_left h.le,max_eq_right h.le]; rfl
    change (visits (Face.lower (x,p) s 0) (oriented (posDir (s.perm a)) (posDir (s.perm b)))).toFinset = (visits _ (oriented (posDir (min _ _)) (posDir (max _ _)))).toFinset
    rw [min_eq_right h.le,max_eq_left h.le,corners,corners, add_right_comm (b := (posDir (s.perm a)).vec)]; ext; simp; tauto
  have ha := visits_aff s 0 x w
  rw [show w.map (·.rotate s)=oriented u v by simp [w,oriented,u,v,← Step.rev_rotate]] at ha
  change (∀ i∈visits x w,_) ↔ _
  simp_rw [← List.mem_toFinset,← he,← ha,List.mem_toFinset]
  simp [hh]

lemma aff_mem (s : Signed) (X : Finset Cover) (hX : X.image s.act=X) (x) : x∈X ↔ s.act x∈X := by
  conv_rhs => lhs; rw [← hX]
  simp [s.act_injective.eq_iff]

/-- Finite **actual** orientations wholly included. -/
def faceSet (X : Finset Cover) : Finset (Face ℤ) := (X ×ˢ univ).filter fun p =>
    ∀ i∈visits p.1 (square p.2.val.1 p.2.val.2), i∈X

def edgeSet (X : Finset Cover) := (X ×ˢ (univ : Finset Axis)).filter fun p => p.1+step p.2∈X

lemma face_set (X : Finset Cover) {G : Gauge} (U : CoverConfig G) :
    faces X U=∑ i ∈ faceSet X,G.chord (faceValue U i) := by
  rw [faceSet,sum_filter,sum_product]; rfl

lemma edge_set (X : Finset Cover) {G : Gauge} (U : CoverConfig G) :
    edges X U=∑ i ∈ edgeSet X,G.chord (U i) := by
  rw [edgeSet,sum_filter,sum_product]; rfl

lemma face_set_image (X : Finset Cover) (s : Signed) (hX : X.image s.act=X) :
    (faceSet X).image (Face.send s 0) = faceSet X := by
  apply eq_of_subset_of_card_le
  · intro x hx; obtain ⟨⟨y,z⟩,hy,rfl⟩ := mem_image.mp hx
    rw [faceSet,mem_filter] at hy ⊢
    have he := (footprint y z s X hX).mp hy.2
    exact ⟨mem_product.mpr ⟨he _ (List.mem_cons_self),mem_univ _⟩, he⟩
  rw [card_image_of_injective _ (Face.injective_send s 0)]

def arcEdge (s : Signed) (e : Edge Cover) : Edge Cover := ((posDir e.2).rotate s).used (s.act e.1)

lemma arc_inj (s : Signed) : Injective (arcEdge s) := by
  rintro ⟨x,i⟩ ⟨y,j⟩ h
  have hs (u : Cover) (a : Axis) : (arcEdge s (u,a)).2=s.perm a := by unfold arcEdge Step.used; split <;> rfl
  have ht : i=j := s.perm.injective <| by rw [← hs x i,← hs y j,h]
  subst j
  suffices x=y by rw [this]
  apply s.act_injective
  unfold arcEdge Step.used at h
  cases he : s.flip i <;> simpa [Step.rotate,posDir,he] using h

lemma edge_image (X : Finset Cover) (s : Signed) (hX : X.image s.act=X) :
    (edgeSet X).image (arcEdge s) = edgeSet X := by
  apply eq_of_subset_of_card_le
  · intro x hx; obtain ⟨⟨y,z⟩,hy,rfl⟩ := mem_image.mp hx
    simp only [edgeSet,mem_filter,mem_product,mem_univ,and_true] at hy ⊢
    have he := (aff_mem s X hX y).mp hy.1
    have ht := (aff_mem s X hX (y+step z)).mp hy.2
    have hq : s.act (step z : Cover)=((posDir z).rotate s).vec := ((posDir z).vec_rotate s).symm
    rw [Signed.act_add,hq] at ht
    cases h : s.flip z
    · simp only [arcEdge, Step.rotate, Step.used,posDir,h,Bool.false_xor,Bool.false_eq_true,↓reduceIte,he,true_and]
      simpa only [Step.rotate,posDir,h,Bool.false_xor,Step.vec,Bool.false_eq_true,↓reduceIte] using ht
    simp only [arcEdge,Step.rotate,posDir,h,Bool.false_xor,Step.used,↓reduceIte,
      sub_add_cancel,he,and_true]; simpa [*,Step.rotate,posDir,Step.vec,sub_eq_add_neg] using ht
  rw [card_image_of_injective _ (arc_inj s)]

lemma channels {G : Gauge} (X : Finset Cover) (U : CoverConfig G) (s : Signed) (hX : X.image s.act=X) :
    faces X (pull s 0 U)=faces X U ∧ edges X (pull s 0 U)=edges X U := by
  rw [face_set,face_set,edge_set,edge_set]
  constructor
  · conv_rhs => rw [← face_set_image X s hX, sum_image (by exact fun _ _ _ _ h => Face.injective_send s 0 h)]
    exact sum_congr rfl fun i _ => Face.send_price U i s 0 G.chord G.chord_inv fun k g => G.chord_conj g k
  conv_rhs => rw [← edge_image X s hX,sum_image (by exact fun _ _ _ _ h => arc_inj s h)]
  apply sum_congr rfl; intro i _
  unfold arcEdge pull Step.read affine; rw [add_zero]; split
  · rw [G.chord_inv]
  rfl
end YM.Axial
