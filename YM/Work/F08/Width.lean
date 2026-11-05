import Mathlib.Analysis.Complex.CauchyIntegral
import YM.Laurent.Rune
import YM.Pressure.Seeds

/-!
Absolute (real-space) convolution estimates for F08.  The budgets are on
Cover, not the quotient; we also identify the periodized actions.  In `routed`, `f` is the kernel for the first step
out from a row; taking step `a` can select *which* kernel to follow next, and
give an effective displacement `d a` in the next scale.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.F08
open Lattice Laurent
open scoped BigOperators

lemma budget_minor {ι : Type*} {f g : ι → ℝ} {A : ℝ} (hg : RG.SumBudget g A)
    (hf : ∀ i, 0 ≤ f i) (hm : ∀ i, f i ≤ g i) : RG.SumBudget f A := by
  have hs := hg.2.1.of_nonneg_of_le hf hm
  exact ⟨hf, hs, (hs.tsum_le_tsum hm hg.2.1).trans hg.2.2⟩

/-- Compose entries routing through the cover. -/
def routed (d : Cover → Cover) (f : Cover → ℝ) (g : Cover → Cover → ℝ) (z : Cover) : ℝ :=
  ∑' a, f a * g a (z - d a)

variable {η A B : ℝ} {d : Cover → Cover} {f : Cover → ℝ} {g : Cover → Cover → ℝ}

lemma paths_budget (hη : 0 ≤ η) (hd : ∀ a, size (d a) ≤ size a)
    (hf : Width η A f) (hg : ∀ a, Width η B (g a)) :
    RG.SumBudget (fun p : Cover × Cover ↦
      Real.exp (η * size p.2) * ‖f p.1 * g p.1 (p.2 - d p.1)‖) (A * B) := by
  let W (z : Cover) := Real.exp (η * size z)
  let F (a : Cover) := W a * ‖f a‖
  let G (a z : Cover) := W z * ‖g a z‖
  let major (p : Cover × Cover) := F p.1 * G p.1 (p.2 - d p.1)
  have hF : RG.SumBudget F A := hf
  have hG (a) : RG.SumBudget (G a) B := hg a
  have hM (p) : 0 ≤ major p := mul_nonneg (hF.1 _) ((hG _).1 _)
  have hs (a : Cover) : Summable fun z ↦ major (a, z) := by
    have he := (Equiv.addRight (-d a)).summable_iff.mpr (hG a).2.1
    have hh : Summable fun z ↦ G a (z - d a) := by
      simpa [Function.comp_def, sub_eq_add_neg] using he
    exact hh.mul_left (F a)
  have cost (a : Cover) : ∑' z, major (a, z) ≤ F a * B := by
    have he : ∑' z, G a (z - d a) = ∑' z, G a z := by
      simpa [sub_eq_add_neg] using ((Equiv.addRight (-d a)).tsum_eq (G a))
    change ∑' z, F a * G a (z - d a) ≤ _
    rw [tsum_mul_left, he]
    exact mul_le_mul_of_nonneg_left (hG _).2.2 (hF.1 _)
  have hL : Summable (fun a ↦ ∑' z, major (a, z)) :=
    (hF.2.1.mul_right B).of_nonneg_of_le (fun a ↦ tsum_nonneg fun z ↦ hM _) cost
  have hprod := (summable_prod_of_nonneg (show 0 ≤ major from hM)).2 ⟨hs, hL⟩
  have bprod : RG.SumBudget major (A * B) := by
    have hB : 0 ≤ B := (tsum_nonneg ((hG 0).1)).trans ((hG 0).2.2)
    refine ⟨hM, hprod, ?_⟩
    calc
      _ = ∑' a, ∑' z, major (a, z) := hprod.tsum_prod
      _ ≤ ∑' a, F a * B := hL.tsum_le_tsum cost (hF.2.1.mul_right B)
      _ = (∑' a, F a) * B := tsum_mul_right
      _ ≤ _ := mul_le_mul_of_nonneg_right hF.2.2 hB
  refine budget_minor bprod (fun _ ↦ by positivity) ?_
  rintro ⟨a, z⟩
  have hlen : size z ≤ size a + size (z - d a) := calc
    _ = size (d a + (z - d a)) := congrArg size (by abel)
    _ ≤ size (d a) + size (z - d a) := size_add _ _
    _ ≤ _ := Nat.add_le_add_right (hd a) _
  have hW : W z ≤ W a * W (z - d a) := by
    unfold W
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) hη)
  change W z * ‖_ * _‖ ≤ F a * G a (z - d a)
  calc
    _ ≤ W a * W (z - d a) * ‖f a * g a (z - d a)‖ :=
      mul_le_mul_of_nonneg_right hW (norm_nonneg _)
    _ = F a * G a (z - d a) := by unfold F G; rw [norm_mul]; ring

lemma paths_safe (hη : 0 ≤ η) (hd : ∀ a, size (d a) ≤ size a)
    (hf : Width η A f) (hg : ∀ a, Width η B (g a)) :
    Summable (fun p : Cover × Cover ↦ ‖f p.1 * g p.1 (p.2 - d p.1)‖) := by
  have hb := paths_budget (η := 0) le_rfl hd (hf.mono hη le_rfl)
    (fun a ↦ (hg a).mono hη le_rfl)
  simpa using hb.2.1

lemma width_routed (hη : 0 ≤ η) (hd : ∀ a, size (d a) ≤ size a)
    (hf : Width η A f) (hg : ∀ a, Width η B (g a)) : Width η (A * B) (routed d f g) := by
  let W (z : Cover) := Real.exp (η * size z)
  let price (p : Cover × Cover) := W p.2 * ‖f p.1 * g p.1 (p.2 - d p.1)‖
  have hb : RG.SumBudget price (A * B) := paths_budget hη hd hf hg
  have hc : (∑' z, ∑' a, price (a, z)) = ∑' p, price p := by
    rw [hb.2.1.tsum_prod]
    exact Summable.tsum_comm (f := fun a z ↦ price (a, z)) hb.2.1
  have hs : Summable (fun z ↦ ∑' a, price (a, z)) :=
    ((summable_prod_of_nonneg (f := fun p ↦ price (Prod.swap p)) (fun p ↦ hb.1 _)).1
      hb.2.1.prod_symm).2
  have hm : RG.SumBudget (fun z ↦ ∑' a, price (a, z)) (A * B) :=
    ⟨fun z ↦ tsum_nonneg (fun a ↦ hb.1 _), hs, hc.trans_le hb.2.2⟩
  unfold Width
  refine budget_minor hm (fun _ ↦ by positivity) ?_
  intro z
  change W z * ‖∑' a, f a * g a (z - d a)‖ ≤ ∑' a, W z * ‖f a * g a (z - d a)‖
  rw [tsum_mul_left]
  have hs' : Summable fun a ↦ ‖f a * g a (z - d a)‖ :=
    (paths_safe hη hd hf hg).prod_symm.prod_factor z
  exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs') (Real.exp_pos _).le

lemma width_sum_finite {ι : Type*} [Fintype ι] {k : ι → Cover → ℝ}
    (h : ∀ i, Width η A (k i)) : Width η (Fintype.card ι * A) (fun z ↦ ∑ i, k i z) := by
  let W (z : Cover) := Real.exp (η * size z)
  let cost (i : ι) (z : Cover) := W z * ‖k i z‖
  have hb (i) : RG.SumBudget (cost i) A := h i
  have hs (i) : Summable (cost i) := (hb i).2.1
  have hm : RG.SumBudget (fun z ↦ ∑ i, cost i z) (Fintype.card ι * A) := by
    refine ⟨fun z ↦ Finset.sum_nonneg fun i _ ↦ (hb _).1 _,
      summable_sum fun i _ ↦ hs i, ?_⟩
    rw [Summable.tsum_finsetSum (fun i _ ↦ hs i)]
    exact (Finset.sum_le_sum fun i _ ↦ (hb i).2.2).trans_eq (by simp)
  unfold Width
  refine budget_minor hm (fun _ ↦ by positivity) ?_
  intro z
  change W z * ‖∑ i, k i z‖ ≤ ∑ i, W z * ‖k i z‖
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (norm_sum_le ..) (Real.exp_pos _).le

/-- Periodize one entry, sign convention of Row.acts. -/
def sift (k : Cover → ℝ) (n : Side) (x y : Site n) :=
  ∑' z, if y = x + wrap n z then k z else 0

lemma summable_sift {n : Side} (hs : Summable f) (x y : Site n) :
    Summable (fun z ↦ if y = x + wrap n z then f z else 0) := by
  have h := hs.indicator {z | y = x + wrap n z}
  exact h.congr fun z ↦ by simp [Set.indicator]

lemma sift_sum_finite {ι : Type*} [Fintype ι] {k : ι → Cover → ℝ}
    (hk : ∀ i, Summable (k i)) (n : Side) (x y : Site n) :
    sift (fun z ↦ ∑ i, k i z) n x y = ∑ i, sift (k i) n x y := by
  unfold sift
  rw [← Summable.tsum_finsetSum (fun i _ ↦ summable_sift (hk i) x y)]
  refine tsum_congr fun z ↦ ?_
  split <;> simp_all only [Finset.sum_const_zero]

/-- Evaluate row times an arbitrary column on the torus via the cover. -/
lemma sift_action (hs : Summable f) (n : Side) (x : Site n) (u : Site n → ℝ) :
    ∑ y, sift f n x y * u y = ∑' a, f a * u (x + wrap n a) := by
  have h (y : Site n) := (summable_sift hs x y).mul_right (u y)
  unfold sift
  simp_rw [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun i _ ↦ h i)]
  refine tsum_congr fun a ↦ ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma sift_routed (hη : 0 ≤ η) (hd : ∀ a, size (d a) ≤ size a)
    (hf : Width η A f) (hg : ∀ a, Width η B (g a)) (n : Side) (x y : Site n) :
    sift (routed d f g) n x y = ∑' a, f a * sift (g a) n (x + wrap n (d a)) y := by
  let steps (a z : Cover) := if y = x + wrap n z then f a * g a (z - d a) else 0
  have hm : Summable (Function.uncurry steps) := by
    have h := (paths_safe hη hd hf hg).of_norm.indicator
      {p : Cover × Cover | y = x + wrap n p.2}
    exact h.congr fun p ↦ by simp [Set.indicator, Function.uncurry, steps]
  calc
    _ = ∑' z, ∑' a, steps a z := by
      refine tsum_congr fun z ↦ ?_
      by_cases he : y = x + wrap n z <;> simp [routed, steps, he]
    _ = ∑' a, ∑' z, steps a z := hm.tsum_comm
    _ = ∑' a, f a * sift (g a) n (x + wrap n (d a)) y := by
      refine tsum_congr fun a ↦ ?_
      rw [← (Equiv.addRight (d a)).tsum_eq (steps a), sift, ← tsum_mul_left]
      refine tsum_congr fun z ↦ ?_
      have he : x + wrap n (z + d a) = (x + wrap n (d a)) + wrap n z := by
        rw [map_add]; abel
      change steps a (z + d a) = _
      simp only [steps, he, add_sub_cancel_right, mul_ite, mul_zero]

end YM.Work.F08
