import YM.RG08.Rate.Shadows

/-!
# Uniform majorants for fine-to-coarse formal recursions

Instead of summing over skipped last factors, use polynomial age majorants with origins
shifted by a *fixed demand-dependent amount*. Then at most half a fixed positive decay exponent
per self step is needed to pay the polynomial variation, EVEN when L varies. For UV difference use
an exponential tilt to reduce to the identical proof. Constants in `Poly` and `Fade` may grow at
strict finite-rank events but cannot change at repeated component steps. In particular an `Array`
here does NOT freeze the cutoff index; that index should be included in X.

No flat/formal Wilson step estimates are assumed by the code definitions. These are general
recurrence solvers; apply them only after proving the strict predecessor-step receipt.
-/
noncomputable section
namespace YM.RG08.Rate.Stair
open Real
open Finset

set_option autoImplicit false
universe v w
variable {X : Type v} {W : Stair X}

/-- Pay the variation of a polynomial with half of the exponential decay. -/
theorem slope (W : Stair X) (x : X) (i : ℕ) (d : ℕ) {θ K : ℝ} (hK : 0 < K) (_hθ : 0 < θ) (h : d ≤ K*θ/2) :
    (K+W.age x (i+1))^d * W.drop θ x i ≤
       (K+W.age x i)^d * W.drop (θ/2) x i := by
  let Δ := W.time x (i+1) - W.time x i
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr ((W.time_strict x).monotone (by omega))
  have ha := W.age_big x i
  have hb := W.age_big x (i+1)
  have hP : K+W.age x i ≥ 0 := by linarith
  have hA : K+W.age x (i+1) ≤ (K+W.age x i) * Real.exp (Δ/K) := by
    have hf := W.age_later x i (i+1) (by omega)
    change W.age x (i+1) ≤ W.age x i+Δ at hf
    calc
      _ ≤ K+W.age x i + Δ := by linarith
      _ ≤ (K+W.age x i) * (1+Δ/K) := by
        field_simp
        nlinarith [mul_nonneg hΔ (show 0 ≤ W.age x i by linarith)]
      _ ≤ _ := by
        gcongr
        rw [add_comm]
        exact Real.add_one_le_exp _
  have hl : d*Δ/K - θ*Δ ≤ -(θ/2)*Δ := by
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right h hΔ]
  calc
    _ ≤ ((K+W.age x i) * Real.exp (Δ/K))^d * W.drop θ x i := by
      gcongr
      exact (W.drop_pos θ x i).le
    _ = (K+W.age x i)^d * Real.exp (d*Δ/K-θ*Δ) := by unfold Stair.drop; rw [mul_pow,← Real.exp_nat_mul,mul_assoc, ← Real.exp_add]; unfold Δ; ring_nf
    _ ≤ _ := by unfold Stair.drop; gcongr

theorem poly_solve {θ : ℝ} (hθ : 0 < θ) {f g : Stair.Array X}
    (hf : ∀ x i, W.Here x i → 0 ≤ f x i) (h : W.Poly g)
    (step : ∀ x i, W.Here x i → f x i ≤ W.stepOnly (fun x i=> f x (i+1)*W.drop θ x i) x i + g x i) :
    W.Poly f := by
  obtain ⟨A,d,hA,hg⟩:=h
  let K : ℝ := 2*(d+1:ℕ)/θ
  let q : ℝ := Real.exp (-(θ/2)*Real.log 3)
  have hK : 0 < K := by unfold K; positivity
  have hQ : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.log_pos (show (1:ℝ)<3 by norm_num)])
  let B := A/(1-q)
  have hB : 0 ≤ B := div_nonneg hA (by linarith)
  let y x i := K + W.age x i
  have hv (x : X) (i : ℕ) : W.drop (θ/2) x i ≤ q := by
    unfold Stair.drop
    apply Real.exp_monotone
    exact mul_le_mul_of_nonpos_left (W.sep_step x i) (by linarith)
  have hc (x : X) (i : ℕ) : f x i ≤ W.stepOnly (fun x i=> f x (i+1)*W.drop θ x i) x i + g x i ∨ ¬ W.Here x i := by by_cases e : W.Here x i; exact Or.inl (step x i e); exact Or.inr e -- maybe unused
  have hBalance : B*q+A=B := by
    unfold B
    field_simp [ne_of_gt (sub_pos.mpr hQ)]
    ring
  have ht (x) (j) : ∀ n i:ℕ, W.top x=n+i→ n≤j→ W.Here x i → f x i ≤ B*y x i^d := by
    induction j with
    | zero =>
      intro n i hi hn hW
      have hz : i=W.top x := by omega
      have hq := step x i hW
      have hr : g x i ≤ A*y x i^d := (hg x i hW).2.trans (by
        unfold y
        gcongr
        · linarith [W.age_big x i]
        · linarith)
      have h₁ : A≤B := by have hh : 0≤q := (Real.exp_pos _).le; nlinarith [mul_nonneg hB hh]
      simp only [Stair.stepOnly,if_neg (show ¬i<W.top x from by omega),zero_add] at hq
      apply (hq.trans hr).trans
      gcongr
      have hyx : 0 ≤ y x i := by unfold y; linarith [W.age_big x i]
      exact pow_nonneg hyx _
    | succ j hj =>
      intro n i ht hn hW
      by_cases h : n ≤ j
      · exact hj n i ht h hW
      have hh : W.top x= j+(i+1) := by omega
      have h₀ : i < W.top x := by omega
      have hp := hj j (i+1) hh (le_refl _) (Stair.finer hW h₀)
      have hyx : 0 ≤ W.age x i := by linarith [W.age_big x i]
      have hy' : 0 ≤ y x i := by unfold y; linarith
      have hq := step x i hW
      simp only [Stair.stepOnly,if_pos h₀] at hq
      calc
        _ ≤ B*y x (i+1)^d*W.drop θ x i + A*y x i^d := hq.trans (add_le_add (mul_le_mul_of_nonneg_right hp (W.drop_pos ..).le) ((hg x i hW).2.trans (by unfold y; gcongr; linarith)))
        _ = B*(y x (i+1)^d*W.drop θ x i) + _ := by rw [mul_assoc]
        _ ≤ B*(y x i^d*q) + _ := by
          gcongr B * ?_ + _
          exact (W.slope x i d hK hθ (by unfold K; push_cast; field_simp; linarith)).trans (mul_le_mul_of_nonneg_left (hv ..) (pow_nonneg hy' _))
        _ = (B*q+A)*y x i^d := by ring
        _ = _ := by rw [hBalance]
  refine ⟨B*(K+1)^d,d,by positivity,fun x i hi=> ⟨hf _ _ hi, (ht x (W.top x-i) (W.top x-i) i (by have h:= hi.2; omega) le_rfl hi).trans ?_⟩⟩
  rw [mul_assoc, ← mul_pow]; unfold y; have hA := W.age_big x i
  gcongr _ * ?_ ^ _
  nlinarith

theorem fade_solve {θ : ℝ} (hθ : 0 < θ) {f g : Stair.Array X}
    (hf : ∀ x i, W.Here x i → 0 ≤ f x i) (h : W.Fade g)
    (step : ∀ x i, W.Here x i → f x i ≤ W.stepOnly (fun x i=> f x (i+1)*W.drop θ x i) x i + g x i) :
    W.Fade f := by
  obtain ⟨c,hc,hg⟩:=h
  let μ := min c (θ/2)
  have hμ : 0 < μ := lt_min hc (by linarith)
  have hu : 0 < θ-μ := sub_pos.mpr (lt_of_le_of_lt (min_le_right ..) (by linarith))
  refine ⟨μ,hμ,poly_solve hu (fun x i hi=>mul_nonneg (hf x i hi) (W.weight_pos ..).le) (Fade.weaker hc hg μ (min_le_left ..)) ?_⟩
  intro x i hi
  have hp:= mul_le_mul_of_nonneg_right (step x i hi) (W.weight_pos μ x i).le
  refine hp.trans_eq ?_
  rw [add_mul]; congr 1
  dsimp [Stair.stepOnly]
  split <;> rename_i hA
  · rw [mul_assoc, weight_step]; ring
  exact zero_mul _

variable {V : Type w}
/-- Self-contraction and strict dependency on any well-founded grade. Use finite V of total
vacuum degree then disposition rank (decreasing), for example. `earn j`: additional forcing and
top stipend can spend polynomial costs on data at grades r strictly below j (including current and
next level). Export the polynomial receipt after assuming the solved bounds on those grades only.
-/
theorem poly_rec {R : V → V → Prop} (h : WellFounded R) (θ : V → ℝ) (hθ : ∀ j, 0 < θ j) (f : V → Array X)
    (hf : ∀ j x i, W.Here x i → 0 ≤ f j x i)
    (earn : ∀ j, (∀ k, R k j → W.Poly (f k)) → ∃ g, W.Poly g ∧ ∀ x i, W.Here x i →
      f j x i ≤ W.stepOnly (fun x i=> f j x (i+1)*W.drop (θ j) x i) x i + g x i) (j : V) : W.Poly (f j) := by
  induction j using h.induction with
  | h j hj =>
    obtain ⟨g,hg,hg'⟩:= earn j hj
    exact poly_solve (hθ j) (hf j) hg hg'

theorem fade_rec {R : V → V → Prop} (h : WellFounded R) (θ : V → ℝ) (hθ : ∀ j, 0 < θ j) (f : V → Array X)
    (hf : ∀ j x i, W.Here x i → 0 ≤ f j x i)
    (earn : ∀ j, (∀ k, R k j → W.Fade (f k)) → ∃ g, W.Fade g ∧ ∀ x i, W.Here x i →
      f j x i ≤ W.stepOnly (fun x i=> f j x (i+1)*W.drop (θ j) x i) x i + g x i) (j : V) : W.Fade (f j) := by
  induction j using h.induction with
  | h j hj =>
    obtain ⟨g,hg,hg'⟩:= earn j hj
    exact fade_solve (hθ j) (hf j) hg hg'

end YM.RG08.Rate.Stair
