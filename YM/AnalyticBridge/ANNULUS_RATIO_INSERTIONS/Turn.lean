import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Motion
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Clean


/-!
# One Forest, tag system and incidence geometry, through the Gaussian bridge

exterior/collar tests on an *oriented* row of `dyed`
vs stores. In particular `replica` is equivariant through signed rotations,
even on tori where a coarse bond may have reversed, even though it does
not assert a canonical lift at the seam. We need the odd block sizes of
this StepData here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented
open SectorNext.Remainder SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma go_flip (s : Signed) (i : Bond n) (hf : s.flip i.2 = true) :
    s.act (i.1 + Lattice.step i.2) = s.act i.1 - Lattice.step (s.perm i.2) := by
  simpa [affine] using StepData.negsite s (0:Site n) i.1 i.2 hf
lemma go_plain (s : Signed) (i : Bond n) (hf : s.flip i.2 = false) :
    s.act (i.1 + Lattice.step i.2) = s.act i.1 + Lattice.step (s.perm i.2) := by
  simpa [affine] using StepData.possite s (0:Site n) i.1 i.2 hf
lemma send_flip (s : Signed) (i : Bond n) (hf : s.flip i.2 = true) :
    sendEdge s 0 i = (s.act i.1 - Lattice.step (s.perm i.2), s.perm i.2) := by
  simp [sendEdge,Step.rotate,posDir,hf,Step.used,affine]
lemma send_plain (s : Signed) (i : Bond n) (hf : s.flip i.2 = false) :
    sendEdge s 0 i = (s.act i.1, s.perm i.2) := by
  simp [sendEdge,Step.rotate,posDir,hf,Step.used,affine]

lemma turn_replica (s : Signed) (V : Config G c) :
    pull s 0 (replica S.ratio V) = replica S.ratio (pull s 0 V) := by
  funext i
  let p := S.ratio
  let j : Bond c := (p.parent i.1,i.2)
  have hx y : p.parent (s.act y) = s.act (p.parent y) := p.parent_signed S.patch.odd_side _ _
  have ht (y z : Site c) : s.act y = s.act z ↔ y=z := s.act_injective.eq_iff
  change pull s 0 (replica p V) i = replica p (pull s 0 V) i
  rw [turn_read]
  change (if _ then (_ : G.El) else _) = (if _ then 1 else pull s 0 V j)
  rw [turn_read]
  cases hr : s.flip i.2
  · simp only [Bool.false_eq_true,↓reduceIte, send_plain s i hr, send_plain s j hr]
    change (if p.parent _ = p.parent _ then _ else _) = _
    rw [← go_plain s i hr, hx,hx]; simp only [ht,j]
  · simp only [↓reduceIte]
    rw [replica, send_flip s i hr,send_flip s j hr]
    simp only [sub_add_cancel]; rw [← go_flip s i hr,hx,hx]; simp only [ht]
    by_cases h : p.parent (i.1+Lattice.step i.2) = p.parent i.1
    · rw [h]; simp
    have he := p.parents_hop S.patch.odd_side i.1 i.2
    split at he
    · rw [if_neg h,if_neg (Ne.symm h),he]
      rw [go_flip s j hr]
    exact (h he).elim

lemma cost_turn (s : Signed) (A : Stores S) (p : Cell f) :
    p ∈ (turnStore s A).costs ↔ faces s f p ∈ A.costs := by simp [turnStore]
lemma aisle_turn (s : Signed) (A : Stores S) (b : Bond c) :
    b ∈ (turnStore s A).aisles ↔ sendEdge s 0 b ∈ A.aisles := by
  change b ∈ _ ↔ StepData.sendBonds s 0 b ∈ A.aisles
  dsimp only [turnStore]; simp
lemma flag_turn (s : Signed) (A : Stores S) (x : Site c) :
    x ∈ (turnStore s A).flags ↔ s.act x ∈ A.flags := by
  have hx : s.act x = StepData.sendSites s 0 x := (add_zero (s.act x)).symm
  dsimp only [turnStore]; rw [hx]; exact Finset.mem_map_equiv

private lemma image_act (s : Signed) {x : Site n} {P : Support n} :
    s.act x ∈ P.image s.act ↔ x∈P := by
  simp [s.act_injective.mem_finset_image]

lemma turn_pin (s : Signed) (x : Site n) (p : Bond n) :
    s.act x ∈ pinPos (sendEdge s 0 p) ↔ x ∈ pinPos p := by
  cases h : s.flip p.2
  · rw [send_plain s p h]; simp only [pinPos, Finset.mem_insert, Finset.mem_singleton, ← go_plain s p h,
      s.act_injective.eq_iff]
  rw [send_flip s p h]; simp only [pinPos, Finset.mem_insert, Finset.mem_singleton, sub_add_cancel]; rw [← go_flip s p h]; simp only [s.act_injective.eq_iff]; rw [or_comm]

lemma turn_start (s : Signed) (x : Site c) (p : Cell f) :
    s.act x ∈ startPos S (faces s f p) ↔ x∈ startPos S p := by
  have he : startPos S (faces s f p) = (startPos S p).image s.act := by
    unfold startPos; change (RG.touched (Face.send s 0 p)).image S.ratio.parent = _
    rw [Work.H03.touched_send,Finset.image_image,Finset.image_image]
    apply Finset.image_congr; intro i _; change S.ratio.parent (affine s 0 i) = s.act (S.ratio.parent i); rw [affine,add_zero,S.ratio.parent_signed S.patch.odd_side]
  rw [he,image_act]

lemma turn_place (s : Signed) (A : Stores S) (x : Site c) :
    x∈(turnStore s A).place ↔ s.act x∈A.place := by
  unfold place; simp only [Finset.mem_union,Finset.mem_biUnion, flag_turn]
  constructor
  · rintro ((⟨p,h,ht⟩|⟨p,h,ht⟩)|h)
    · exact Or.inl (Or.inl ⟨faces s f p,(cost_turn ..).mp h,(turn_start ..).mpr ht⟩)
    · exact Or.inl (Or.inr ⟨sendEdge s 0 p,(aisle_turn ..).mp h,(turn_pin ..).mpr ht⟩)
    exact Or.inr h
  rintro ((⟨p,h,ht⟩|⟨p,h,ht⟩)|h)
  · obtain ⟨p,rfl⟩ := (faces s f).surjective p
    exact Or.inl (Or.inl ⟨p,(cost_turn ..).mpr h,(turn_start ..).mp ht⟩)
  · obtain ⟨p,rfl⟩ := (StepData.sendBonds s 0).surjective p
    exact Or.inl (Or.inr ⟨p,(aisle_turn ..).mpr h,(turn_pin ..).mp ht⟩)
  exact Or.inr h

lemma turn_dome (s : Signed) (A : Stores S) (x : Site c) (b : ℕ) :
    x∈(turnStore s A).dome b ↔ s.act x∈A.dome b := by
  unfold dome; rw [halo_spec,halo_spec]
  constructor
  · rintro ⟨y,h,hx⟩; exact ⟨s.act y,(turn_place ..).mp h,(separation_signed y x s).trans_le hx⟩
  rintro ⟨y,h,hx⟩
  obtain ⟨y,rfl⟩ := s.actEquiv.surjective y
  exact ⟨y,(turn_place ..).mpr h,(separation_signed y x s) ▸ hx⟩

lemma turn_incidence (s : Signed) (R Q R' Q' : Support c)
    (h : ∀ x, x∈R' ↔ s.act x∈R) (he : ∀ x,x∈Q' ↔ s.act x∈Q) :
    Disjoint R' Q' ↔ Disjoint R Q := by
  simp_rw [Finset.disjoint_left]
  constructor
  · intro hh i hi ht
    obtain ⟨j,rfl⟩ := s.actEquiv.surjective i
    exact hh ((h j).mpr hi) ((he j).mpr ht)
  intro hh i hi ht; exact hh ((h i).mp hi) ((he i).mp ht)



lemma turn_mass (s : Signed) {U : Config G f} {k : S.Choices} (hm : S.patch.Branches S.kernel G) (i : Site c) :
    S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) (pull s 0 U)) ((choice s k).1 i) =
      S.patch.frameMass S.kernel (expandAt (S.ratio.embed (s.act i)) U) (k.1 (s.act i)) := by
  have he : S.withinSites s 0 (choice s k).1 = k.1 := congr_arg Prod.fst ((S.withinChoice s 0).apply_symm_apply k)
  rw [expandAt_pull,affine,add_zero,← Ratio.signed,(S.patch.frames_channel hm ..).1,← S.port_site s 0]
  rw [affine,add_zero,he]

/-- Through the whole local halo (so we will not need Alive globally for the payment). -/
lemma turn_wide (s : Signed) {D : ℕ} {x w : ℝ} {O A : Stores S} {U : Config G f} {k : S.Choices} {V : Config G c}
    (hm : S.patch.Branches S.kernel G) (h : Affine.Wide O A D x w U k V) : Affine.Wide
      (turnStore s O) (turnStore s A) D x w (pull s 0 U) (choice s k) (pull s 0 V) := by
  constructor
  · intro i hi
    have he : toll (pull s 0 U) i = toll U (faces s f i) :=
      Face.send_price U i s 0 G.chord G.chord_inv fun k g => G.chord_conj g k
    simp only [cost_turn,he]
    apply h.consumes
    exact mt (turn_incidence s _ _ _ _ (fun x => turn_dome s ..) (fun x => (turn_start s x i).symm)).mpr hi
  · intro i hi
    simp only [aisle_turn,(carry s hm k U).2,wire_pulled]
    apply h.drive
    exact mt (turn_incidence s _ _ _ _ (fun x => turn_dome s ..) (fun x => (turn_pin s x i).symm)).mpr hi
  · intro i hi
    have hh := Work.H03.flags_send s (0:Site c) (temp x) V
    rw [show affine s (0:Site c) = s.act from funext fun i => add_zero _] at hh
    rw [flag_turn,h.precise (s.act i) ((turn_dome ..).mp hi),← hh,image_act]
  intro i hi
  rw [turn_mass s hm i]; exact h.list _ ((turn_dome ..).mp hi)

end YM.AnalyticBridge.AnnulusRatioInsertions
