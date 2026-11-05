import YM.Analysis.Polydisc
import YM.Bid.Tar

/-! # Absolute-coordinate tube dual positivity via relative gaps -/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C10
open Set Filter Boundary
open scoped Topology BigOperators InnerProductSpace

lemma peel {n : ℕ} (p : Points n) (i : Fin n) :
    suffixP p i.val - suffixP p (i.val + 1) = p i := by
  unfold suffixP
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h
    by_cases H : i.val ≤ j.val
    · have : i.val + 1 ≤ j.val := by omega
      simp [H, this]
    · have : ¬ i.val + 1 ≤ j.val := by omega
      simp [H, this]
  · simp

lemma telescope {n : ℕ} {p : Points (n + 1)} (hp : p ∈ coneM (n + 1)) (y : Points (n + 1)) :
    inner ℝ p y = ∑ i : Fin n, inner ℝ (suffixP p (i.val + 1)) (y i.succ - y i.castSucc) := by
  calc
    inner ℝ p y = ∑ i : Fin (n + 1), (inner ℝ (suffixP p i.val) (y i) -
        inner ℝ (suffixP p (i.val + 1)) (y i)) := by
      rw [PiLp.inner_apply]; exact Finset.sum_congr rfl fun i _ => by rw [← inner_sub_left, peel]
    _ = _ := by
      rw [Finset.sum_sub_distrib, Fin.sum_univ_succ (fun i => inner ℝ (suffixP p i.val) (y i)),
        Fin.sum_univ_castSucc (fun i => inner ℝ (suffixP p (i.val + 1)) (y i))]
      simp_rw [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last, total hp, after_n,
        inner_zero_left, zero_add, add_zero, inner_sub_right, Finset.sum_sub_distrib]

lemma rim {n : ℕ} {p y : Points n} (hp : p ∈ coneM n) (hy : y ∈ shores n) : 0 ≤ inner ℝ p y := by
  cases n with
  | zero => simp [PiLp.inner_apply]
  | succ n =>
    rw [telescope hp]
    apply Finset.sum_nonneg
    intro i _
    apply Mink.self_pair (sees hp _)
    simp only [shores, mem_iInter, mem_setOf_eq] at hy
    exact hy i.castSucc i.succ rfl

lemma cone_bound {n : ℕ} (y : Points n) (hy : y ∈ fields n) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ u in 𝓝 y, ∀ p ∈ coneM n, c * ‖p‖ ≤ inner ℝ p u := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ((smooth_fields n).mem_nhds hy)
  have hc := half_pos hr
  refine ⟨r / 2, hc, Filter.mem_of_superset (Metric.ball_mem_nhds y hc) ?_⟩
  intro u hu p hp
  by_cases h : p = 0
  · simp [h]
  have hn := norm_pos_iff.mpr h
  let v := (r / 2 / ‖p‖) • p
  have he : r / 2 / ‖p‖ * ‖p‖ = r / 2 := div_mul_cancel₀ _ hn.ne'
  have hv : ‖v‖ = r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hc hn), he]
  have H : u - v ∈ Metric.ball y r := by
    have Hd := dist_triangle (u-v) u y
    rw [dist_eq_norm (u-v) u, sub_right_comm, sub_self, zero_sub, norm_neg, hv] at Hd
    change dist u y < r / 2 at hu
    change dist _ _ < _
    linarith
  have hY := rim hp (warmer n (hball H))
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_mul_norm, ← mul_assoc, he] at hY
  exact sub_nonneg.mp hY

theorem answer : YM.Bid.C10 := fun _ => ⟨fun _ _ => rim, cone_bound⟩
end YM.Work.C10
