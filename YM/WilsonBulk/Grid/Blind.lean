import YM.Work.F08.Rows
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Newtown
import Mathlib.Data.Set.Finite.List
import YM.Push.ABSOLUTE_SUMS.Basic

/-!
# Killing discrete moments on the Wilson bulk grid

Use the coefficient space & real-space sign convention of `Laurent.Width` and `Bloch.Row`.
All differences, including ones used when varying UV cutoff, are taken on the *cover*.

`Blind k f`: the row kills all scalar arrays polynomial of total position degree < k.
We characterize such tests by killing length-k strings of forward differences, so can use
summation by parts without choosing positive stubs or multiindex powers. There is NO spatial
truncation in this definition. Check summability of every application (never use `tsum` as a
predicate without it). Rooted frame/stencil uses below need also translation compatibility.
-/

namespace YM.WilsonBulk
noncomputable section
open Lattice Laurent Filter Function
open MultiNext.SignedSource MultiNext.SignedSource.Newt
open Push.AbsoluteSums
open Work.F08
open scoped Topology BigOperators

abbrev span (x : Cover) : ℝ := (size x : ℝ)

/-- Our tests include negative integer offsets. -/
def DegLess (k : ℕ) (F : Cover → ℝ) := ∀ l : List Axis, l.length = k → Newt.iterate F l = 0

lemma degLess_zero {F} : DegLess 0 F ↔ F = 0 :=
  ⟨fun h => h [] rfl, fun h l hl => by subst F; simp [List.length_eq_zero_iff.mp hl, iterate]⟩

lemma degLess_succ {F k} : DegLess (k+1) F ↔ ∀ i, DegLess k (jump F i) := by
  constructor
  · intro h i l hl
    exact h (i::l) (by simp [hl])
  · intro h l hl
    cases l with
    | nil => simp at hl
    | cons i l => apply h i l; simpa using hl

lemma jump_take (p : Cover → ℝ) (k : ℕ) (i : Axis) :
    jump (Newt.take (k+1) p) i = Newt.take k (jump p i) := by
  have h := currency k p i
  funext x
  have hX := congrFun h x
  dsimp only [jump, tail] at hX ⊢
  linarith

lemma degLess_take (k : ℕ) (p : Cover → ℝ) : DegLess k (Newt.take k p) := by
  induction k generalizing p with
  | zero => apply degLess_zero.mpr; ext x; simp only [Newt.take, Finset.range_zero, Finset.sum_empty]; rfl
  | succ k ih => apply degLess_succ.mpr; intro i; rw [jump_take]; exact ih _

lemma DegLess.tail_zero {p k} (h : DegLess k p) (x) : Newt.tail k p x = 0 := by
  apply norm_le_zero_iff.mp
  simpa using! Newt.localized k (p:=p) (M:=0) le_rfl (span x)
    (fun l hl z _ => by rw [h l hl]; simp) x le_rfl

lemma DegLess.take_same {p k} (h : DegLess k p) : Newt.take k p = p :=
  funext fun x => (sub_eq_zero.mp (h.tail_zero x)).symm

/-- For moving sums across pairings. -/
def PowerBound (p : Cover → ℝ) (d : ℕ) := ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖p x‖ ≤ M * (1 + span x)^d

-- Need only existential here (paired polynomials, not the residual estimate).
lemma piece_power (k : ℕ) (p : Cover → ℝ) : PowerBound (fun x => Newt.piece k p (Pattern.xyz x)) k := by
  classical
  let s := (List.finite_length_eq Axis k).toFinset
  let M := ∑ l ∈ s, ‖Newt.iterate p l 0‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hr (l : List Axis) (hl : l.length = k) : ‖Newt.iterate p l 0‖ ≤ M :=
    Finset.single_le_sum (f:=fun l => ‖Newt.iterate p l 0‖)
      (fun l _ => norm_nonneg _) (show l ∈ s by simp [s, hl])
  refine ⟨(4*((k:ℝ)+1))^k * M, by positivity, fun x => ?_⟩
  exact (component k p hM hr x).trans_eq (by ring)

lemma PowerBound.widen {p i k} (h : PowerBound p i) (he : i ≤ k) : PowerBound p k := by
  obtain ⟨M, hM, hf⟩ := h
  refine ⟨M,hM,fun x => (hf x).trans (mul_le_mul_of_nonneg_left ?_ hM)⟩
  exact pow_le_pow_right₀ (by dsimp [span]; simp) he

lemma take_power (k : ℕ) (p : Cover → ℝ) : PowerBound (Newt.take k p) k := by
  choose c hc h using fun i => piece_power i p
  refine ⟨∑ i ∈ Finset.range k, c i, Finset.sum_nonneg fun i _ => hc _, fun x=>?_⟩
  rw [Finset.sum_mul]; apply (norm_sum_le ..).trans
  refine Finset.sum_le_sum fun i hi => ?_
  exact (h i x).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp [span])
    (Nat.le_of_lt (Finset.mem_range.mp hi))) (hc i))

lemma DegLess.power {p k} (h : DegLess k p) : PowerBound p k := by
  simpa only [h.take_same] using take_power k p

lemma test_budget {w : ℝ} {d : ℕ} (x : Cover) (hw : 0 < w) :
    (1 + span x)^d ≤ (w⁻¹ ^ d * d.factorial * Real.exp w) * Real.exp (w * span x) :=
  polynomial_cost hw (by positivity) _

lemma budget_pairing {σ a M : ℝ} {p f : Cover → ℝ} (hp : Width σ a p) (hM : 0 ≤ M)
    (hf : ∀ x, ‖f x‖ ≤ M * Real.exp (σ * span x)) :
    RG.SumBudget (fun x => ‖p x * f x‖) (M*a) := by
  refine budget_minor (budget_scale hM hp) (fun x => norm_nonneg _) fun x => ?_
  change ‖p x * f x‖ ≤ M*(Real.exp (σ * span x) * ‖p x‖)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _)).trans_eq (by ring)

lemma finite_pairing {σ a : ℝ} (hσ : 0 < σ) {p f : Cover → ℝ} (hp : Width σ a p)
    {d : ℕ} (hf : PowerBound f d) : Summable (fun x => p x * f x) := by
  obtain ⟨M,hM,H⟩ := hf
  have hF (x) : ‖f x‖ ≤ (M * (σ⁻¹ ^ d * d.factorial * Real.exp σ)) * Real.exp (σ * span x) :=
    (H x).trans ((mul_le_mul_of_nonneg_left (test_budget x hσ) hM).trans_eq
      (by rw [mul_assoc M _ (Real.exp _)]))
  exact (budget_pairing hp (by positivity) hF).2.1.of_norm

def Blind (k : ℕ) (f : Cover → ℝ) := ∀ p : Cover → ℝ, DegLess k p → HasSum (fun x => f x * p x) 0

lemma Blind.erase {p k} (h : Blind k p) (f : Cover → ℝ) :
    HasSum (fun x => p x * Newt.take k f x) 0 := h (Newt.take k f) (degLess_take k f)

end
end YM.WilsonBulk
