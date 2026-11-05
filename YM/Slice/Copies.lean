import YM.Slice.Independent
import YM.Cells.Interior

/-!
# Factor the integrand apart from indicated cross seams

Applies to bounded measurable probes LocalOn the strict positive sector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open Function Set Filter MeasureTheory Lattice Wilson Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {G : Gauge} (C : Cut n)

/-- Standard filler elsewhere, does not force any of the weight couplings when pairing. -/
def reader (K : Posts C G) (P : Open C G) := follow C ((K,1),P,P)

private lemma alongPos {P Q : Circle G C.pos n} (hl : ∀ i : Inner C, (P i).1=(Q i).1)
    (ht : ∀ i : Steps C, (P i).2=(Q i).2) : Agrees C.sector (chain C.pos P) (chain C.pos Q) := by
  rintro ⟨x,j⟩ hx he
  change x + step j ∈ C.sector at he
  have hp : Plus C (x C.pos) := hx
  unfold chain
  dsimp only
  split_ifs with H
  · have hh : Plus C (x C.pos + 1) := by
      subst j
      change Plus C ((x+step C.pos : Site n) C.pos) at he; simpa using he
    rw [ht ⟨_, strict_thread hp hh⟩]
  rw [hl ⟨_,hp⟩]

lemma first_eye (p : Dwelling C G) : Agrees C.sector (chain C.pos (follow C p))
    (chain C.pos (reader C p.1.1 p.2.1)) := by
  apply alongPos C (by intro i; simp only [reader,follow,hit]) (by intro i; simp only [reader,follow,pointed])

lemma second_eye (p : Dwelling C G) : Agrees C.sector (C.pullC G (chain C.pos (follow C p)))
    (chain C.pos (reader C p.1.1 p.2.2)) := by
  rw [mirrors]
  apply alongPos C (by intro i; simp only [reader,follow,hit,opposite,hitOpp,replace])
  intro i
  simp only [reader]
  change (((follow C p (imageChord C i)).2)⁻¹) = _
  simp [follow, pointed_back, replace]

private lemma forwardLook (p : Dwelling C G) {x : Per n} (hx : ¬ Plus C (level C x)) :
    (follow C p x).1 = (reader C p.1.1 p.2.1 x).1 := by
  by_cases h : Plus C x
  · unfold reader follow; rw [hit C (⟨x,h⟩ : Inner C),hit C (⟨x,h⟩ : Inner C)]
  have he : x ∈ pier C := ⟨h,hx⟩
  unfold reader follow; rw [seam C ⟨x,he⟩, seam C ⟨x,he⟩]

private lemma rearLook (p : Dwelling C G) {x : Per n} (hx : ¬ Plus C (level C x)) :
    (follow C p (level C x)).1 = (reader C p.1.1 p.2.2 x).1 := by
  by_cases h : Plus C x
  · unfold reader follow; rw [hitOpp C (⟨x,h⟩ : Inner C),hit C (⟨x,h⟩ : Inner C)]; rfl
  have he : x ∈ pier C := ⟨h,hx⟩
  unfold reader follow; rw [fixed_pier he,seam C ⟨x,he⟩, seam C ⟨x,he⟩]

variable (β : ℝ)

def area (K : Posts C G) (P : Open C G) :=
  ∏ i : Steps C, weight C.pos β (reader C K P i).1 (reader C K P (i.val+1)).1 (reader C K P i).2

def rim (P : Dwelling C G) :=
  ∏ i : ↥(gate C), weight C.pos β (follow C P i).1 (follow C P (i.val+1)).1 (follow C P i).2

lemma class_bijection : Function.Bijective (Sum.elim (Sum.elim (fun i : Steps C => i.val) (fun i : Steps C => imageChord C i))
      (fun i : ↥(gate C) => i.val)) := by
    constructor
    · rintro ((i|i)|i) ((j|j)|j) H <;> simp only [Sum.elim_inl,Sum.elim_inr] at H
      · rw [show i=j from Subtype.ext H]
      · exact (opposite_time j.property (H ▸ i.property)).elim
      · exact (j.property.1 (H ▸ i.property)).elim
      · exact (opposite_time i.property (H.symm ▸ j.property)).elim
      · have hw : Involutive (imageChord C) := chord_turn C
        rw [show i=j from Subtype.ext (hw.injective H)]
      · have hV : imageChord C j.val=i.val := by rw [← show imageChord C i=j.val from H,chord_turn]
        exact (j.property.2 (hV.symm ▸ i.property)).elim
      · exact (i.property.1 (H.symm ▸ j.property)).elim
      · have hV : imageChord C i.val=j.val := by rw [← show imageChord C j=i.val from H.symm,chord_turn];
        exact (i.property.2 (hV.symm ▸ j.property)).elim
      rw [show i=j from Subtype.ext H]
    intro x
    by_cases h : bridge C x
    · exact ⟨Sum.inl (Sum.inl ⟨x,h⟩),rfl⟩
    by_cases hv : bridge C (imageChord C x)
    · exact ⟨Sum.inl (Sum.inr ⟨_,hv⟩),chord_turn C x⟩
    exact ⟨Sum.inr ⟨x,h,hv⟩,rfl⟩

lemma includes (v : Dwelling C G) : bare β (chain C.pos (follow C v)) =
    area C β v.1.1 v.2.1 * area C β v.1.1 v.2.2 * rim C β v := by
  classical
  let W := follow C v
  let f (i : Per n) := weight C.pos β (W i).1 (W (i+1)).1 (W i).2
  rw [totalWeight]
  change ∏ i, f i = _
  rw [← Equiv.prod_comp (Equiv.ofBijective _ (class_bijection C)) f]; simp only [Fintype.prod_sum_type,Equiv.ofBijective_apply,
    Sum.elim_inl,Sum.elim_inr]
  unfold area rim
  refine congr_arg₂ (· * ·) (congr_arg₂ (· * ·) ?_ ?_) rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h := thread_ends i.property
    unfold f
    rw [show (W i).1 = _ from forwardLook C v h.1, show (W _).1 = _ from forwardLook C v h.2]
    simp only [W,reader,follow,pointed]
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨h,p⟩ := thread_ends i.property
  have h₁ : level C i.val = imageChord C i + 1 := by rw [imageChord]; ring
  have h₂ := (chord_end C i.val).symm
  have hx : (W (imageChord C i.val)).2 = ((reader C v.1.1 v.2.2 i).2)⁻¹ := by simp [reader,W,follow,replace]
  unfold f
  rw [← h₁,hx, show (W (level C i)).1 = _ from rearLook C v h, show (W (imageChord C i)).1 = _ from
    congr_arg (fun x => (W x).1) h₂ |>.trans (rearLook C v p), weight_reflect]
end YM.Slice
