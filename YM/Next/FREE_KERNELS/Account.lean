import YM.Next.FREE_KERNELS.Lines

/-!
# Symmetry and reality currency

`Silver z` means ordinary nonnegative real at the argument in question. All
Fourier formulas use multiplication in ℂ; reality here is for the evaluation
on the real slice, not for analytical adjoints off that slice.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

def Silver (z : ℂ) := ∃ x : ℝ, 0 ≤ x ∧ z=(x:ℂ)

namespace Silver
variable {z w : ℂ}
lemma real {x : ℝ} (h : 0≤x) : Silver (x:ℂ) := ⟨_,h,rfl⟩
lemma zero : Silver 0 := real (x:=0) le_rfl
lemma one : Silver 1 := real (x:=1) zero_le_one
lemma re_nonneg (h : Silver z) : 0 ≤ z.re := by obtain ⟨a,ha,rfl⟩ := h; exact ha
lemma of_real (h : Silver z) : (z.re:ℂ)=z := by obtain ⟨a,ha,rfl⟩ := h; rfl
lemma norm (h : Silver z) : ‖z‖=z.re := by obtain ⟨a,ha,rfl⟩ := h; rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha]; rfl
lemma fixed (h : Silver z) : star z=z := by obtain ⟨a,ha,rfl⟩ := h; simp
lemma add (h : Silver z) (h' : Silver w) : Silver (z+w) := by
  obtain ⟨a,ha,rfl⟩ := h; obtain ⟨b,hb,rfl⟩ := h'
  rw [← Complex.ofReal_add]; exact real (add_nonneg ha hb)
lemma mul (h : Silver z) (h' : Silver w) : Silver (z*w) := by
  obtain ⟨a,ha,rfl⟩ := h; obtain ⟨b,hb,rfl⟩ := h'
  rw [← Complex.ofReal_mul]; exact real (mul_nonneg ha hb)
lemma inv (h : Silver z) : Silver z⁻¹ := by
  obtain ⟨a,ha,rfl⟩ := h; rw [← Complex.ofReal_inv]; exact real (inv_nonneg.mpr ha)
lemma gram (x : ℂ) : Silver (x*star x) := by rw [Complex.star_def,Complex.mul_conj]; exact real (Complex.normSq_nonneg _)
lemma div (h : Silver z) (h' : Silver w) : Silver (z/w) := by rw [div_eq_mul_inv]; exact h.mul h'.inv
lemma pow (h : Silver z) (i : ℕ) : Silver (z^i) := by
  induction i with
  | zero => rw [pow_zero]; exact Silver.one
  | succ i hi => rw [pow_succ]; exact hi.mul h
lemma sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i∈s, Silver (f i)) : Silver (∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Silver.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]; exact (h a (Finset.mem_insert_self ..)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
lemma side (L : Side) : Silver (L.val:ℂ) := by exact_mod_cast real (side_pos L).le
lemma chipSq (M : Side) {p : Momentum} (hp : physical p) : Silver (divisor M p) := by rw [divisor_normSq M hp]; exact real (by positivity)
lemma re_ne {x : ℂ} (h : Silver x) (hx : x≠0) : 0 < x.re := h.norm ▸ norm_pos_iff.mpr hx
end Silver

/-- Periodicity adapted to Cover. -/
def Stable (f : Momentum → ℂ) : Prop := ∀ p x, f (p+reciprocal x)=f p

/-- No mod L qualifications in D summands other than the actual fine periods. -/
lemma shuttle_stable (L : Side) (f : Momentum → ℂ) (h : Stable f) : Stable (fun p => ∑ i : Site L, f (aliasAt p i)) := by
  intro p x
  calc
    _ = ∑ i : Site L, f (aliasAt p (i+wrap L x)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      obtain ⟨j,hj⟩ := alias_exchange p i x
      rw [hj,h]
    _ = _ := Equiv.sum_comp (Equiv.addRight (wrap L x)) (fun i => f (aliasAt p i))

lemma reciprocal_negate (x : Cover) : reciprocal (-x)=-reciprocal x := by ext i; simp [reciprocal]
lemma chipSq_stable : Stable (divisor 1) := by
  intro p x; simp only [divisor,seedQ,narrow_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he : (-(p+reciprocal x))=(-p)+reciprocal (-x) := by rw [reciprocal_negate]; abel
  rw [he]
  have hh (p : Momentum) (x : Cover) : chip ((p+reciprocal x) i / ((1:Side).val:ℂ))=chip (p i / ((1:Side).val:ℂ)) := by simpa [reciprocal] using chip_repeat (p i) (x i)
  rw [hh,hh]

lemma lift_signed {L : Side} (ho : Odd L.val) (s : Signed) (l : Site L) : lift (s.act l)=s.act (lift l) := by
  refine lift_eq_iff.mpr ⟨?_,?_⟩
  · rw [← wrap_signed,wrap_lift]
  intro i; obtain ⟨j,rfl⟩ := s.perm.surjective i
  have hx := centers_odd l ho j
  rw [Signed.act_at]; split <;> omega

lemma alias_signed {L : Side} (ho : Odd L.val) (s : Signed) (p : Momentum) (l : Site L) :
    aliasAt (s.act p) (s.act l)=s.act (aliasAt p l) := by
  ext i
  obtain ⟨i,rfl⟩ := s.perm.surjective i
  simp only [alias_value,lift_signed ho,Signed.act_at]
  split <;> simp only [Int.cast_neg]; ring

lemma chipSq_signed (M : Side) (p : Momentum) (s : Signed) : divisor M (s.act p)=divisor M p := by
  unfold divisor; rw [← Equiv.sum_comp s.perm (fun i => seedQ M (s.act p) i * seedQ M (-s.act p) i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [seedQ,narrow_apply, Pi.neg_apply, Signed.act_at]; split <;> simp only [neg_neg]; ring
end YM.Next.Free
