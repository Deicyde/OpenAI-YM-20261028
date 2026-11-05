import YM.Further.GAUSSIAN_SCALAR_LEDGER.Gaussian
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.GridCost
import YM.Progress.STATIONARY_SCENES.Green
import YM.Push.STATIONARY_UNIFORM.Count
import YM.SectorNext.VACUUM_NORMALIZATION.Round



set_option warningAsError false

/-!
# From precision estimates to uniform scalar window errors

Uses actual principal compressions of the **complete** Gram
(identity completions harmless). A coarse or fine distance can be
supplied; multiplicity of coordinates per site paid. Include any window
which puts outsiders far away; no symmetry of the choice asserted. Get
post-L invoices on exponential absolute row & column sums, *assuming*
uniform gap and exponentially costed rows on A. Scalar, no V
differentiation or mask-support persistence.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function Filter Precision SectorNext.Vacuum Lattice
open Round (rowRate)
open YM.Progress.StationaryScenes.Green
open YM.Push.Uniform (Multiplicity Multiplicity.count Decay countCost count_pos decay_pos)
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {c : Side} {ι : Type*} [Fintype ι]

/-- May repeat positions for many color/link slots. -/
abbrev Double (sites : ι → Site c) (γ K : ℝ) (A : Wall ι) := Both sites sites A γ K K
namespace Double

variable {l : ι → Site c} {γ K : ℝ} {A T : Wall ι} (h : Double l γ K A)

include h in
lemma point (i j : ι) : wt γ (l i) (l j)*|A i j| ≤ K :=
  (Finset.single_le_sum (f := fun j => wt γ (l i) (l j)*|A i j|)
    (fun _ _ => mul_nonneg (wt_pos ..).le (abs_nonneg _)) (Finset.mem_univ j)).trans (h.1 i)

lemma fromEntries {l : ι → Site c} {γ δ K : ℝ} (hK : 0 ≤ K) (h : δ < γ) {N : ℕ} (hp : Multiplicity l N)
    (he : ∀ i j, wt γ (l i) (l j)*|A i j| ≤ K) : Double l δ (K*(N*countCost (γ-δ))) A := by
  have hb (X : Wall ι) (hb : ∀ i j, wt γ (l i) (l j)*|X i j| ≤ K) :
      Rows l l X δ (K*(N*countCost (γ-δ))) := by
    intro i
    apply le_trans _ (mul_le_mul_of_nonneg_left (Multiplicity.count l hp (sub_pos.mpr h) (l i)) hK)
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro j _
    have he : wt δ (l i) (l j)=wt γ (l i) (l j)*Decay (γ-δ) (l i) (l j) := by
      unfold wt Decay; rw [← Real.exp_add]; congr 1; ring
    rw [he, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (hb i j) (decay_pos ..).le
  exact ⟨hb A he,hb Aᵀ (fun i j => by rw [wt_symm]; exact he j i)⟩

include h

lemma loosen {r : ℝ} (hr : γ ≥ r) : Double l r K A := by
  have hx (X : Wall ι) (h : Rows l l X γ K) : Rows l l X r K := by
    intro i; apply le_trans _ (h i); refine Finset.sum_le_sum fun j _ => ?_
    unfold wt; gcongr
  exact ⟨hx _ h.1,hx _ h.2⟩

lemma ease {L : ℝ} (hp : K ≤ L) : Double l γ L A := ⟨fun i=>(h.1 i).trans hp,fun i=>(h.2 i).trans hp⟩

lemma into_rate (hp : 0 ≤ γ) : Round.rowRate K A ∧ Round.rowRate K Aᵀ := by
  have hc : Double l 0 K A := loosen h hp
  exact ⟨fun i => by simpa [wt] using hc.1 i, fun i => by simpa [wt] using hc.2 i⟩

lemma mirror : Double l γ K Aᵀ := ⟨h.2, by simpa using h.1⟩
lemma play (b : ℝ) : Double l γ (|b| * K) (b • A) := by
  have hb := h.2.pay b
  exact ⟨h.1.pay b, by rwa [transpose_smul]⟩
lemma add {L : ℝ} (g : Double l γ L T) : Double l γ (K+L) (A+T) :=
  ⟨h.1.plus g.1, by rw [transpose_add]; exact h.2.plus g.2⟩
lemma times {L : ℝ} (hz : 0 ≤ γ) (hK : 0 ≤ K) (hL : 0 ≤ L) (g : Double l γ L T) :
    Double l γ (K*L) (A*T) :=
  ⟨Rows.multiply hz h.1 g.1 hL, by rw [mul_comm K L,transpose_mul]; exact Rows.multiply hz g.2 h.2 hK⟩
end Double

/-- W_i per column including center. -/
structure Lens (ι : Type*) where
  eye : ι → Finset ι
  sees (i : ι) : i ∈ eye i
namespace Lens

variable (Z : Lens ι)

def Outside (l : ι → Site c) (size : ℝ) := ∀ i j, i ∉ Z.eye j → size ≤ separation (l i) (l j)

variable [DecidableEq ι]

def center (i : ι) : (↥(Z.eye i)) := ⟨i,Z.sees i⟩
def glass (A : Wall ι) (i : ι) : Wall (↥(Z.eye i)) := A.submatrix Subtype.val Subtype.val

def plus (A : Wall ι) (u : ℝ) := A + u • (1 : Wall ι)
def visit (A : Wall ι) (u : ℝ) : Wall ι := Matrix.of fun j i =>
    if h : j ∈ Z.eye i then ((plus (Z.glass A i) u)⁻¹) ⟨j,h⟩ (Z.center i) else 0

def missed (A : Wall ι) (u : ℝ) : Wall ι := plus A u * Z.visit A u - 1

def full (A : Wall ι) (u : ℝ) := (plus A u)⁻¹

omit [Fintype ι] in
@[simp] lemma visit_here (A : Wall ι) (u : ℝ) (i : ι) (j : (Z.eye i)) :
    Z.visit A u (↑j) i = ((plus (Z.glass A i) u)⁻¹) j (Z.center i) := by
  unfold visit; rw [Matrix.of_apply,dif_pos j.property]

omit [Fintype ι] in
lemma addPrice (A : Wall ι) (u : ℝ) (i : ι) : Z.glass (plus A u) i=plus (Z.glass A i) u := by
  ext j k
  change plus A u j k = _
  by_cases h : j=k
  · subst j; simp [plus,glass]
  have he : j.val ≠ k.val := fun ht => h (Subtype.ext ht)
  simp [plus,glass,h,he]

omit [Fintype ι] in
lemma plus_pos {A : Wall ι} (h : A.PosDef) {u : ℝ} (hu : 0 ≤ u) : (plus A u).PosDef := by
  refine h.add_posSemidef ?_
  exact Matrix.PosSemidef.smul Matrix.PosSemidef.one hu

omit [Fintype ι] in
lemma invert {A : Wall ι} (h : A.PosDef) {u : ℝ} (hu : 0 ≤ u) (i : ι) :
    (Z.glass (plus A u) i).PosDef := (plus_pos h hu).submatrix Subtype.val_injective

lemma sight {A : Wall ι} (h : A.PosDef) {u : ℝ} (hu : 0 ≤ u) (i j : ι) (he : i ∈ Z.eye j) :
    Z.missed A u i j = 0 := by
  have hp := (Z.invert h hu j).det_pos
  rw [Z.addPrice] at hp
  let W := plus (Z.glass A j) u
  have hw : W * W⁻¹ = 1 := W.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hp.ne')
  unfold missed; rw [Matrix.sub_apply, sub_eq_zero]
  let l : (↥(Z.eye j)) := ⟨i,he⟩
  calc
    _ = ∑ k∈Z.eye j, plus A u i k * Z.visit A u k j := by
      rw [Matrix.mul_apply]; symm; exact Finset.sum_subset (Finset.subset_univ _) fun k _ hk => by
        unfold visit; rw [Matrix.of_apply,dif_neg hk,mul_zero]
    _ = ∑ k : (Z.eye j), W l k * W⁻¹ k (Z.center j) := by
      rw [← Finset.sum_attach _ (fun k => plus A u i k * Z.visit A u k j)]
      apply Finset.sum_congr rfl; intro k _
      rw [visit_here, show plus A u i (↑k) = W l k from congr_fun (congr_fun (Z.addPrice A u j) l) k]
    _ = (1 : Wall (↥(Z.eye j))) l (Z.center j) := congr_fun (congr_fun hw l) (Z.center j)
    _ = _ := by
      by_cases h : i=j
      · subst i; rw [show l = Z.center j from rfl]; simp
      have hh : l≠Z.center j := fun he => h (congr_arg Subtype.val he)
      simp [hh,h]

lemma lost (A : Wall ι) (u : ℝ) (i j : ι) (he : i ∉ Z.eye j) :
    Z.missed A u i j = (A*Z.visit A u) i j := by
  have hh : i≠j := by rintro rfl; exact he (Z.sees _)
  unfold missed plus
  simp only [Matrix.sub_apply,Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply_ne hh]
  simp [visit,he]

lemma rebuilds {A : Wall ι} (h : A.PosDef) {u : ℝ} (hu : 0 ≤ u) :
    full A u + full A u * Z.missed A u=Z.visit A u := by
  unfold full missed
  rw [Matrix.mul_sub, ← mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (plus_pos h hu).det_pos.ne'),
    mul_one,one_mul]; abel

end Lens
end YM.Further.GaussianScalar
