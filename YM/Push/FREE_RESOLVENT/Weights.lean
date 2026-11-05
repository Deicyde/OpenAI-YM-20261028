import Mathlib.Analysis.SpecialFunctions.Log.Basic




/-!
# Absolute weighted Schur bounds

Counting on the *actual finite index sets*. The locations may coincide,
may already have been projected to block coordinates, etc. No cutting off
in the definition of the weight. Keep row & column separately so multiplicity
in different rectangle directions can be priced differently. No tacit factors
sqrt(volume) from comparing Pi norms. Includes empty index sets.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix
open scoped BigOperators

/-- Pseudodistance; using data rather than an instance so we can work with
several costs on the same indices. -/
structure Cost (X : Type*) where
  d : X → X → ℝ
  nonneg (x y : X) : 0 ≤ d x y
  self (x : X) : d x x = 0
  comm (x y : X) : d x y = d y x
  triangle (x y z : X) : d x z ≤ d x y + d y z

namespace Cost
variable {X Y ι κ μ : Type*}
variable (D : Cost X)

def pull (f : Y → X) : Cost Y :=
  ⟨fun x y => D.d (f x) (f y), fun _ _ => D.nonneg .., fun _ => D.self _,
    fun _ _ => D.comm .., fun _ _ _ => D.triangle ..⟩

def weight (σ : ℝ) (x y : X) : ℝ := Real.exp (σ * D.d x y)

lemma weight_pos (σ : ℝ) (x y : X) : 0 < D.weight σ x y := Real.exp_pos _
lemma weight_nn (σ : ℝ) (x y : X) : 0 ≤ D.weight σ x y := (D.weight_pos ..).le
@[simp] lemma weight_self (σ : ℝ) (x : X) : D.weight σ x x = 1 := by simp [weight, D.self]
lemma weight_symm (σ : ℝ) (x y : X) : D.weight σ x y = D.weight σ y x := by rw [weight,D.comm,weight]
@[simp] lemma weight_zero (x y : X) : D.weight 0 x y = 1 := by simp [weight]
lemma weight_mono {σ σ' : ℝ} (h : σ ≤ σ') (x y : X) : D.weight σ x y ≤ D.weight σ' x y :=
  Real.exp_monotone (mul_le_mul_of_nonneg_right h (D.nonneg ..))
lemma weight_triangle {σ : ℝ} (h : 0 ≤ σ) (x y z : X) :
    D.weight σ x z ≤ D.weight σ x y * D.weight σ y z := by
  simp only [weight, ← Real.exp_add, Real.exp_le_exp, ← mul_add]
  exact mul_le_mul_of_nonneg_left (D.triangle ..) h
lemma weight_add (σ σ' : ℝ) (x y : X) :
    D.weight (σ+σ') x y = D.weight σ x y * D.weight σ' x y := by simp [weight,add_mul,Real.exp_add]
lemma weight_neg (σ : ℝ) (x y : X) : D.weight (-σ) x y = (D.weight σ x y)⁻¹ := by simp [weight,Real.exp_neg]
lemma weight_shrink {γ σ R : ℝ} (h : γ ≤ σ) {x y : X} (hx : R ≤ D.d x y) :
    D.weight γ x y ≤ Real.exp (-(σ-γ)*R) * D.weight σ x y := by
  rw [weight, weight, ← Real.exp_add, Real.exp_le_exp]; nlinarith only [mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr h)]

/-- Note row and column roles (the kernel `A : Matrix ι κ ℝ` maps κ-vectors to ι-vectors). -/
structure Rows [Fintype κ] (a : ι → X) (b : κ → X) (σ M : ℝ) (A : Matrix ι κ ℝ) : Prop where
  bound (i : ι) : ∑ j, D.weight σ (a i) (b j) * |A i j| ≤ M

structure Schur [Fintype ι] [Fintype κ] (a : ι → X) (b : κ → X) (σ M : ℝ) (A : Matrix ι κ ℝ) : Prop where
  rows : D.Rows a b σ M A
  cols : D.Rows b a σ M A.transpose

/-- For pointwise to weighted-sum conversions. Points counted WITH all
multiplicities (in particular all colors). -/
structure Volume [Fintype ι] (a : ι → X) (σ M : ℝ) : Prop where
  bound (x : X) : ∑ i, D.weight (-σ) x (a i) ≤ M

lemma Volume.le {D : Cost X} {a : ι → X} [Fintype ι] {σ M N : ℝ} (h : D.Volume a σ M)
    (hM : M ≤ N) : D.Volume a σ N := ⟨fun x => (h.bound x).trans hM⟩

lemma sum_comp_le {ι κ : Type*} [Fintype ι] [Fintype κ] {f : ι → κ}
    (h : Function.Injective f) (g : κ → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, g (f i) ≤ ∑ i, g i := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image f, g j := (Finset.sum_image (fun _ _ _ _ e => h e)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hg _

lemma Volume.comp {D : Cost X} {a : ι → X} [Fintype ι] [Fintype κ] {σ M : ℝ} (h : D.Volume a σ M)
    {e : κ → ι} (he : Function.Injective e) : D.Volume (a ∘ e) σ M := by
  constructor; intro x
  exact (sum_comp_le he (fun i => D.weight (-σ) x (a i)) fun _ => D.weight_nn ..).trans (h.bound x)

namespace Rows
variable {D} {a : ι → X} {b : κ → X} {c : μ → X} {σ γ M N : ℝ} {A B : Matrix ι κ ℝ} [Fintype κ]

lemma weighted (h : D.Rows a b σ M A) (i j) : D.weight σ (a i) (b j) * |A i j| ≤ M := by
  apply le_trans ?_ (h.bound i)
  exact Finset.single_le_sum (fun j _ => mul_nonneg (D.weight_nn ..) (abs_nonneg _)) (Finset.mem_univ j)
lemma point (h : D.Rows a b σ M A) (i j) : |A i j| ≤ D.weight (-σ) (a i) (b j) * M := by
  rw [weight_neg, inv_mul_eq_div, le_div_iff₀ (weight_pos ..), mul_comm]
  exact h.weighted ..
lemma of_point (hM : 0 ≤ M)
    (h : ∀ i j, |A i j| ≤ D.weight (-σ) (a i) (b j) * M) (hv : D.Volume b (σ-γ) N) :
    D.Rows a b γ (N*M) A := by
  constructor; intro i
  refine le_trans (Finset.sum_le_sum (g := fun j => D.weight (-(σ-γ)) (a i) (b j)*M) fun j _ => ?_) ?_
  · apply (mul_le_mul_of_nonneg_left (h i j) (D.weight_nn ..)).trans_eq
    rw [← mul_assoc, ← weight_add]; congr 2; ring
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hv.bound _) hM
lemma zero (hM : 0 ≤ M) : D.Rows a b σ M 0 := ⟨by simp [hM]⟩
lemma one {a : κ → X} [DecidableEq κ] : D.Rows a a σ 1 1 := by
  constructor; intro i; simp [Matrix.one_apply, apply_ite abs]
lemma mono (h : D.Rows a b σ M A) (hg : γ ≤ σ) (hl : M ≤ N) : D.Rows a b γ N A := by
  constructor; intro i
  exact (Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    mul_le_mul_of_nonneg_right (weight_mono D hg (a i) (b j)) (abs_nonneg (A i j)))).trans ((h.bound i).trans hl)
lemma abs_le (h : D.Rows a b σ M A) (he : ∀ i j, |B i j| ≤ |A i j|) : D.Rows a b σ M B := by
  constructor; intro i
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (h.bound i)
  exact mul_le_mul_of_nonneg_left (he i j) (D.weight_nn ..)
lemma neg (h : D.Rows a b σ M A) : D.Rows a b σ M (-A) := h.abs_le (by simp)
lemma smul (h : D.Rows a b σ M A) (r : ℝ) : D.Rows a b σ (|r| *M) (r • A) := by
  constructor; intro i
  simpa only [Matrix.smul_apply, smul_eq_mul, _root_.abs_mul, mul_left_comm (D.weight _ _ _) |r|,
    ← Finset.mul_sum] using (mul_le_mul_of_nonneg_left (h.bound i) (abs_nonneg r))
lemma add (hA : D.Rows a b σ M A) (hB : D.Rows a b σ N B) : D.Rows a b σ (M+N) (A+B) := by
  constructor; intro i
  apply le_trans ?_ (add_le_add (hA.bound i) (hB.bound i))
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_add_le ..) (D.weight_nn ..)
lemma sub (hA : D.Rows a b σ M A) (hB : D.Rows a b σ N B) : D.Rows a b σ (M+N) (A-B) := by
  rw [sub_eq_add_neg]; exact hA.add hB.neg

/-- Bound a cut-away portion using width strictly reserved in A. Does not
require positivity of R or γ; meaningful savings when R>0 & γ<σ. -/
lemma far (hA : D.Rows a b σ M A) (R : ℝ) (hg : γ ≤ σ)
    (hs : ∀ i j, B i j ≠ 0 → R ≤ D.d (a i) (b j)) (he : ∀ i j, |B i j| ≤ |A i j|) :
    D.Rows a b γ (Real.exp (-(σ-γ)*R)*M) B := by
  constructor; intro i
  apply le_trans ?_ (mul_le_mul_of_nonneg_left (hA.bound i) (Real.exp_pos _).le)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h : B i j = 0
  · rw [h, abs_zero, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (D.weight_nn ..) (abs_nonneg _))
  rw [← mul_assoc]
  exact mul_le_mul (D.weight_shrink hg (hs i j h)) (he i j) (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le (D.weight_nn ..))

lemma submatrix {ι' ν : Type*} [Fintype ν] (e : ι' → ι) {f : ν → κ}
    (hf : Function.Injective f) (hA : D.Rows a b σ M A) :
    D.Rows (a ∘ e) (b ∘ f) σ M (A.submatrix e f) := by
  constructor; intro i
  exact (sum_comp_le hf (fun j => D.weight σ (a (e i)) (b j) * |A (e i) j|) fun j =>
    mul_nonneg (D.weight_nn ..) (abs_nonneg _)).trans (hA.bound _)

-- expose the pointwise convolution too
lemma term_mul (h : 0 ≤ σ) (a : ι → X) (b : κ → X) (c : μ → X) (A : Matrix ι κ ℝ) (B : Matrix κ μ ℝ) (i l) :
    D.weight σ (a i) (c l) * |(A*B) i l| ≤
      ∑ j, (D.weight σ (a i) (b j)*|A i j|)*(D.weight σ (b j) (c l)*|B j l|) := by
  rw [Matrix.mul_apply]
  refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (D.weight_nn ..)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [_root_.abs_mul]
  apply (mul_le_mul_of_nonneg_right (D.weight_triangle h _ (b j) _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq
  ring

lemma mul [Fintype μ] {B : Matrix κ μ ℝ} (hA : D.Rows a b σ M A) (hB : D.Rows b c σ N B) (hσ : 0 ≤ σ) (hN : 0 ≤ N) :
    D.Rows a c σ (M*N) (A*B) := by
  constructor; intro i
  refine (Finset.sum_le_sum (fun l _ => term_mul (D := D) hσ a b c A B i l)).trans ?_
  rw [Finset.sum_comm]
  apply le_trans ?_ (mul_le_mul_of_nonneg_right (hA.bound i) hN)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hB.bound j) (mul_nonneg (D.weight_nn ..) (abs_nonneg _))
end Rows

namespace Schur
variable {D} {a : ι → X} {b : κ → X} {c : μ → X} {σ γ M N : ℝ} {A B : Matrix ι κ ℝ} [Fintype ι] [Fintype κ]
lemma mono (h : D.Schur a b σ M A) (hg : γ ≤ σ) (hl : M ≤ N) : D.Schur a b γ N A :=
  ⟨h.rows.mono hg hl, h.cols.mono hg hl⟩
lemma zero (hM : 0 ≤ M) : D.Schur a b σ M 0 := ⟨Rows.zero hM, Rows.zero hM⟩
lemma one [DecidableEq ι] : D.Schur a a σ 1 1 := ⟨Rows.one, by rw [transpose_one]; exact Rows.one⟩
lemma transpose (h : D.Schur a b σ M A) : D.Schur b a σ M A.transpose := ⟨h.cols,h.rows⟩
lemma abs_le (h : D.Schur a b σ M A) (he : ∀ i j, |B i j| ≤ |A i j|) : D.Schur a b σ M B :=
  ⟨h.rows.abs_le he,h.cols.abs_le fun i j => he j i⟩
lemma neg (h : D.Schur a b σ M A) : D.Schur a b σ M (-A) := ⟨h.rows.neg,h.cols.neg⟩
lemma smul (h : D.Schur a b σ M A) (r : ℝ) : D.Schur a b σ (|r| *M) (r • A) :=
  ⟨h.rows.smul r,h.cols.smul r⟩
lemma add (hA : D.Schur a b σ M A) (hB : D.Schur a b σ N B) : D.Schur a b σ (M+N) (A+B) :=
  ⟨hA.rows.add hB.rows,hA.cols.add hB.cols⟩
lemma sub (hA : D.Schur a b σ M A) (hB : D.Schur a b σ N B) : D.Schur a b σ (M+N) (A-B) :=
  ⟨hA.rows.sub hB.rows,hA.cols.sub hB.cols⟩
lemma submatrix {ι' ν : Type*} [Fintype ι'] [Fintype ν] {e : ι' → ι} {f : ν → κ}
    (he : Function.Injective e) (hf : Function.Injective f) (hA : D.Schur a b σ M A) :
    D.Schur (a ∘ e) (b ∘ f) σ M (A.submatrix e f) :=
  ⟨Rows.submatrix _ hf hA.rows,Rows.submatrix _ he hA.cols⟩
lemma mul [Fintype μ] {B : Matrix κ μ ℝ} (hA : D.Schur a b σ M A) (hB : D.Schur b c σ N B)
    (hσ : 0 ≤ σ) (hM : 0 ≤ M) (hN : 0 ≤ N) : D.Schur a c σ (M*N) (A*B) := by
  refine ⟨hA.rows.mul hB.rows hσ hN,?_⟩
  rw [transpose_mul, mul_comm M]; exact hB.cols.mul hA.cols hσ hM
lemma far (hA : D.Schur a b σ M A) (R : ℝ) (hg : γ ≤ σ)
    (hs : ∀ i j, B i j ≠ 0 → R ≤ D.d (a i) (b j)) (he : ∀ i j, |B i j| ≤ |A i j|) :
    D.Schur a b γ (Real.exp (-(σ-γ)*R)*M) B := by
  refine ⟨hA.rows.far R hg hs he,hA.cols.far R hg (fun i j h => (hs j i h).trans_eq (D.comm ..)) fun i j => he j i⟩
lemma of_point (hM : 0 ≤ M)
    (h : ∀ i j, |A i j| ≤ D.weight (-σ) (a i) (b j) * M) (hv : D.Volume b (σ-γ) N)
    (hw : D.Volume a (σ-γ) N) : D.Schur a b γ (N*M) A :=
  ⟨Rows.of_point hM h hv, Rows.of_point hM (fun i j => by rw [weight_symm]; exact h j i) hw⟩
end Schur
end Cost
end YM.FreeResolvent
