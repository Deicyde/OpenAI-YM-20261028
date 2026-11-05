import YM.Exterior.Initial

/-!
# Uniform control about the harmonic

Use the sizes of the one-step differences `q` directly, so no
representative in a fundamental momentum cube has to be picked.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F06
open Lattice Laurent Bloch Exterior Finset Matrix
open scoped BigOperators Topology

lemma within_real {η : ℝ} {p : Momentum} (hη : 0 ≤ η) (hp : star p = p) : Within η p := by
  intro i
  rw [Complex.conj_eq_iff_im.mp (congr_fun hp i), abs_zero]
  exact hη

lemma mode_add_bound (p : Momentum) (hp : star p = p) (x y : Cover) :
    ‖mode p (x + y) - 1‖ ≤ ‖mode p x - 1‖ + ‖mode p y - 1‖ := by
  rw [mode_shift, show mode p x * mode p y - 1 =
    (mode p x - 1) * mode p y + (mode p y - 1) by ring]
  apply (norm_add_le ..).trans
  rw [Complex.norm_mul, mode_real p y hp, mul_one]

lemma mode_neg_depart (p : Momentum) (hp : star p = p) (x : Cover) :
    ‖mode p (-x) - 1‖ = ‖mode p x - 1‖ := by
  rw [← mode_adjoint, hp, show star (mode p x) - 1 = star (mode p x - 1) by simp,
    norm_star]

lemma mode_depart (p : Momentum) (hp : star p = p) (x : Cover) (δ : ℝ)
    (hδ : ∀ i, ‖q p i‖ ≤ δ) : ‖mode p x - 1‖ ≤ (size x : ℝ) * δ := by
  have hn (i : Axis) (k : ℕ) : ‖mode p (k • step i) - 1‖ ≤ (k:ℝ)*δ := by
    induction k with
    | zero => simp
    | succ k ih =>
      have he : ‖mode p (step i) - 1‖ ≤ δ := by rw [factor]; exact hδ i
      rw [add_smul, one_smul, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      exact (mode_add_bound p hp _ _).trans (add_le_add ih he)
  let f : Axis → Cover := fun i => x i • step i
  have hz (i : Axis) : ‖mode p (f i) - 1‖ ≤ ((x i).natAbs:ℝ)*δ := by
    unfold f
    cases x i with
    | ofNat n => simpa only [Int.natAbs_natCast, Int.ofNat_eq_natCast, natCast_zsmul] using hn i n
    | negSucc n => rw [negSucc_zsmul, mode_neg_depart p hp]; exact hn i _
  have h (s : Finset Axis) : ‖mode p (∑ i∈s, f i) - 1‖ ≤ ∑ i∈s, ((x i).natAbs:ℝ)*δ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [sum_insert hi, sum_insert hi]
      exact (mode_add_bound p hp _ _).trans (add_le_add (hz i) ih)
  have hx : ∑ i, f i = x := by
    funext i
    simp [Finset.sum_apply, f, zsmul_eq_mul, mul_ite]
  simpa only [hx, size, Nat.cast_sum, Finset.sum_mul] using h univ

variable {α β : Type*}

lemma row_entry_le {R : Row α β} {η A : ℝ} (hr : R.strip η A) (hη : 0 ≤ η)
    (p : Momentum) (hp : star p = p) (i : α) (j : β) : ‖R.read p i j‖ ≤ A :=
  Width.estimate (Row.constant_strip R hr i j) p (within_real hη hp)

lemma row_entry_depart {R : Row α β} {η A : ℝ} (hr : R.strip η A) (hη : 0 < η)
    (p : Momentum) (hp : star p = p) (δ : ℝ) (hd : 0 ≤ δ) (he : ∀ i, ‖q p i‖ ≤ δ)
    (i : α) (j : β) : ‖R.read p i j - R.read 0 i j‖ ≤ δ / η * A := by
  let f := fun z : Cover => (R i j z:ℂ)
  have hw : Width η A f := Row.constant_strip R hr i j
  let u := fun t : Momentum => fun z : Cover => mode t z • f z
  change ‖(∑' z, u p z) - ∑' z, u 0 z‖ ≤ _
  have hs (t : Momentum) (ht : star t = t) : Summable (u t) :=
    (hw.series t (within_real hη.le ht)).2.1.of_norm
  rw [← (hs p hp).tsum_sub (hs 0 (by simp))]
  let g := fun z : Cover => Real.exp (η * size z) * ‖f z‖
  have hpay (z : Cover) : ‖u p z - u 0 z‖ ≤ δ / η * g z := by
    have hl : η * size z ≤ Real.exp (η * size z) := by
      linarith [Real.add_one_le_exp (η * size z)]
    unfold u g
    rw [mode_constant, ← sub_smul, norm_smul, ← mul_assoc _ _ ‖f z‖]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖mode p z - 1‖ ≤ (size z:ℝ)*δ := mode_depart p hp z δ he
      _ = δ/η*(η*size z) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  have hg : Summable fun z : Cover => δ / η * g z :=
    (show Summable g from hw.2.1).mul_left _
  have hf : Summable fun z => ‖u p z - u 0 z‖ :=
    hg.of_nonneg_of_le (fun _ => norm_nonneg _) hpay
  refine (norm_tsum_le_tsum_norm hf).trans ((hf.tsum_le_tsum hpay hg).trans ?_)
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hw.2.2 (by positivity)

open Filter in
lemma row_entry_hlimit {R : Row α β} {η A : ℝ} (hr : R.strip η A) (hη : 0 < η)
    {ι : Type*} {l : Filter ι} (p : ι → Momentum) (hp : ∀ a, star (p a) = p a)
    (h : ∀ k : Axis, Tendsto (fun a => q (p a) k) l (𝓝 0)) (i : α) (j : β) :
    Tendsto (fun a => R.read (p a) i j) l (𝓝 (R.read 0 i j)) := by
  let δ (a : ι) := ∑ k, ‖q (p a) k‖
  have hd : Tendsto δ l (𝓝 0) := by
    have hb (k : Axis) : Tendsto (fun a => ‖q (p a) k‖) l (𝓝 0) := by
      simpa using (h k).norm
    simpa only [Finset.sum_const_zero] using (tendsto_finsetSum Finset.univ (fun k _ => hb k))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (g:=fun a => δ a / η * A) (fun a => ?_) ?_
  · refine row_entry_depart hr hη _ (hp a) _ (by unfold δ; positivity) (fun k => ?_) i j
    exact Finset.single_le_sum (fun b _ => norm_nonneg (q (p a) b)) (mem_univ k)
  simpa using (hd.div_const η).mul_const A

end YM.Work.F06
