import YM.Next.FOUNDATIONS.LinkBounds
/-!
Helpers for polynomial directional cancellation. Use homogeneous real tensor
coefficients. Degrees here are in *position* (`E4`) when applied to link
components; not source factor orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter Tensor Next.Foundations
open scoped Topology BigOperators ContDiff Classical

section
variable {E F Y Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {f g : E → F} {n j m : ℕ}

def Degree (n : ℕ) (f : E → F) : Prop := ∃ a : ∀ j, T E F j, f = ∑ i∈ Finset.range (n+1), diagonal (a i)

namespace Degree

protected lemma diag (hn : j ≤ n) (A : T E F j) : Degree n (diagonal A) := by
  let a : ∀ i, T E F i := Pi.single j A
  refine ⟨a, Eq.symm ?_⟩
  rw [Finset.sum_eq_single j, show a j = A from Pi.single_eq_same ..]
  · intro i _ hi; rw [show a i=0 from Pi.single_eq_of_ne hi _]; rfl
  intro h; exact (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))).elim
protected lemma add (h : Degree n f) (ht : Degree n g) : Degree n (f+g) := by
  obtain ⟨a,ha⟩ := h; obtain ⟨b,hb⟩ := ht
  exact ⟨a+b, funext fun i => by simp [ha,hb,diagonal,Finset.sum_apply,Finset.sum_add_distrib]⟩
protected lemma smul (h : Degree n f) (t : ℝ) : Degree n (t • f) := by
  obtain ⟨a,ha⟩ := h
  exact ⟨t • a, funext fun i => by simp [ha,diagonal,Finset.sum_apply,Finset.smul_sum]⟩
protected lemma sub (h : Degree n f) (ht : Degree n g) : Degree n (f-g) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ]; exact h.add (ht.smul _)

protected lemma homog (hf : ContDiffAt ℝ n f 0) (he : ∀ x : E, ∀ t : ℝ, f (t • x) = t^n • f x) :
    diagonal (coeff f n 0) = f := by
  funext i
  have ht (z : ℝ) : f (z • i) = z^n • f i := he i z
  have h : ContDiffAt ℝ n (fun x : ℝ => x^n) 0 := (contDiffAt_id.pow n)
  change (n.factorial:ℝ)⁻¹ • diagonal (iteratedFDeriv ℝ n f 0) i = _
  rw [← iteratedDeriv_on_line hf, funext ht, iteratedDeriv_smul_const h,iteratedDeriv_pow]; simp [smul_smul, Nat.descFactorial_self,Nat.factorial_ne_zero]
protected lemma of_hom (hf : ContDiffAt ℝ n f 0) (he : ∀ x : E, ∀ t : ℝ, f (t • x) = t^n • f x) : Degree n f :=
  Degree.homog hf he ▸ Degree.diag (le_refl n) (coeff f n 0)
protected lemma const (x : F) (n : ℕ) : Degree n (fun _ : E => x) := by
  have he : diagonal (coeff (fun _ : E => x) 0 0)=_ := Degree.homog (by simpa using (contDiffAt_const (x:=(0:E)) (c:=x) (n:=(0:WithTop ℕ∞)) (𝕜:=ℝ))) (by simp)
  exact he ▸ Degree.diag (Nat.zero_le n) (coeff (fun _ : E => x) 0 0)

protected lemma sum {ι : Type*} (s : Finset ι) {f : ι → E → F} (h : ∀ i∈s, Degree n (f i)) :
    Degree n (∑ i∈s, f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Degree.const 0 n
  | insert i s hi ih => rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))
protected lemma mono (h : Degree n f) (hm : n ≤ m) : Degree m f := by
  obtain ⟨a,ha⟩ := h
  rw [ha]; exact Degree.sum _ fun i hi => Degree.diag ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hm) _

protected lemma linear (h : Degree n f) (L : F →L[ℝ] Y) : Degree n (L ∘ f) := by
  obtain ⟨a,ha⟩ := h; refine ⟨fun i => L.compContinuousMultilinearMap (a i),?_⟩
  ext; simp [ha,Function.comp, Finset.sum_apply, diagonal]


/-- Multilinear polynomials with different slot degrees. -/
protected theorem tensor (T' : T F Z m) (f : Fin m → E → F) (p : Fin m → ℕ)
    (hf : ∀ i, Degree (p i) (f i)) : Degree (∑ i, p i) (fun x => T' (fun i => f i x)) := by
  choose a ha using hf
  let s i := Finset.range (p i+1)
  let c (r : Fin m → ℕ) (x : E) := T' fun i => diagonal (a i (r i)) x
  have hm r (hr : r ∈ Fintype.piFinset s) : (∑ i, r i) ≤ ∑ i, p i := Finset.sum_le_sum fun i _ =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hr i))
  have h x : T' (fun i => f i x) = ∑ r ∈ Fintype.piFinset s, c r x := by
    simp_rw [ha, Finset.sum_apply]; exact T'.map_sum_finset (fun i j => diagonal (a i j) x) s
  simp_rw [funext h, ← Finset.sum_apply (g:=c)]
  apply Degree.sum _; intro r hr
  apply Degree.mono _ (hm r hr)
  apply Degree.of_hom
  · exact (T'.contDiff.comp (contDiff_pi.mpr fun i => diag_smooth (a i (r i)) _)).contDiffAt
  intro x t; unfold c; simp_rw [homogeneous,T'.map_smul_univ,Finset.prod_pow_eq_pow_sum]
end Degree
end
end YM.Planned.AtomRegular
