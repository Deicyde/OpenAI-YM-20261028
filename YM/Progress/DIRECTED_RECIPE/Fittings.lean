import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Recipe
import YM.Progress.DIRECTED_RECIPE.Vacuum

/-!
# Sampling Input port for RG work from separate budgets

Support/placement transport Fittings still required.

No assertion that
any physical estimator or kernel decomposition satisfies these charges.

Maintains ALL epsilon orders for parameter tests.

Full-order E.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe.Payments
open Function Set RG Wilson Lattice RG.Shoot Ovens Ovens.Pipes
open Next.Scheduling RG.Supply MeasureTheory Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n : Side} {d : ℝ → Tap G n} {P : BudgetPoint} {X : Pipes G n}

/-- A test directly on the soft logarithm, not on gathered data. -/
lemma steady {T : Set ℝ}
    (he : ∀ x∈T, ∀ i, ∃ C : ℝ, ∀ U, ‖(d x).logarithm i U‖ ≤ C)
    (ht : ∀ x∈T, ∀ i, Varies (fun x => (d x).logarithm i) x T ∧
      Varies (fun x => (d x).forced i) x T) (P : BudgetPoint) : invariantJet P d T := by
  intro x hx i ε hp
  cases i with
  | inl i =>
    filter_upwards [(ht x hx i).2 ε hp] with y hy U
    rw [abs_sub_comm]; exact hy U
  | inr i =>
    obtain ⟨C,hC⟩ := he x hx i
    have hy := Varies.exp (ht x hx i).1 (C:=Real.exp C) (fun u =>
      Real.exp_monotone ((le_abs_self _).trans (hC u))) (Real.exp_pos _)
    filter_upwards [hy ε hp] with y hy U
    rw [abs_sub_comm]; simp only [reach,Sum.elim_inr,sub_sub_sub_cancel_right]; exact hy U

-- for a startup with one common bound (step also gets a sequence-only payment option through `switched`)


/-- Only at fixed volume. No uniform point payments on `PreBound` in y
are inferred. -/
lemma pre_finite {p q : ℕ → ℝ} {T : Set ℝ} (ha : T.Nonempty) (ht : Summable p) (hu : Summable q)
    (hs : ∀ x∈T,rooted (d x) p q) (H : ∃ c : ℕ → ℝ, Summable c ∧ ∀ x∈T, ∀ i,
      P.supBounds (X.reg i).site (X.reg i).support ((d x).regular i) (c i)) : PreBound P d X T := by
  -- no assuming q≤1 across sequences; use a Lipschitz estimate with arbitrarily-large common C
  obtain ⟨x,hx⟩ := ha
  have hq i : 0 ≤ q i := (norm_nonneg _).trans (hs x hx i 1).2
  let C := ∑' i, q i
  have he i : q i ≤ C := by simpa only [Finset.sum_singleton] using hu.sum_le_tsum {i} (fun i _ => hq i)
  let f := Sum.elim p (fun i => Real.exp C*q i)
  have hz : 0≤C := tsum_nonneg hq
  refine ⟨H,f,Summable.sum f ht (hu.mul_left _),?_⟩
  rintro y hy (i|i) U
  · exact (hs y hy i U).1
  let a := (d y).logarithm i U
  have ha : |a| ≤ q i := (hs y hy i U).2
  change ‖Real.exp a-1‖ ≤ _
  have hg : |Real.exp a - 1| ≤ Real.exp C * |a| := by
    by_cases H : 0 ≤ a
    · rw [abs_of_nonneg H, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp H))]
      calc
        Real.exp a-1 ≤ Real.exp a * a := by
          have h := Real.add_one_le_exp (-a)
          have he := mul_le_mul_of_nonneg_left h (Real.exp_nonneg a)
          rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at he
          linarith only [he]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_monotone ((le_abs_self _).trans (ha.trans (he i)))) H
    have he' := le_of_not_ge H
    rw [abs_of_nonpos he', abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr he'))]
    have hg : -(Real.exp a - 1) ≤ -a := by linarith [Real.add_one_le_exp a]
    exact hg.trans (le_mul_of_one_le_left (neg_nonneg.mpr he') (Real.one_le_exp hz))
  exact hg.trans (mul_le_mul_of_nonneg_left ha (Real.exp_nonneg _))

open Precision
variable {a : Levels G} {M : Horizon a} {O : ChartRatio G} {k : Kin M O} {r : Permissions a}
variable {s : Survey G} {v : ℕ → ℕ} {q : Quote} {D : Rolls (s.paper q v)}
variable {T : Protection D} {W : Delays T} {Y : Bar W} {Z : Wait Y} {F : ℕ → ℕ → Postage}
variable {N m p : ℕ} {Gf : ∀ i j, Pairing (F i j)}




end YM.Progress.DirectedRecipe.Payments
