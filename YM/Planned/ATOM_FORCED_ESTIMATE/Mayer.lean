import YM.Push.LOCAL_SPLITTING.Calculus

/-!
# Finite order cost of one exponential missing-address factor

For the negative logarithm-cluster copies in E jxtr (and related exponential
attachments): use one `exp(-term)-1` per numbered address, grouping copies of that
identical address with their exponential factorials. Derivatives only before the mask.
Preserves the overlap incidence; the Mayer expression itself has the very same mask.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.Forced
open Lattice Wilson RG Push.Local Filter Next.Foundations Function
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side}

def mayer (f : Config G n → ℂ) (V : Config G n) := Complex.exp (f V) - 1

def mayerCost : ℕ → ℝ
 | 0 => 3
 | k+1 => 2^k*mayerCost k

lemma mayerCost_three_le (k : ℕ) : 3 ≤ mayerCost k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num)))

section Jets
variable {f : Config G n → ℂ} {U : Config G n}

private lemma heads (h : Chart 1 f U) (A : Directions G n) :
    leftDerivs (Complex.exp ∘ f) [A] U = (Complex.exp ∘ f) U * leftDerivs f [A] U ∧
    leftDerivs (mayer f) [A] U = (Complex.exp ∘ f) U * leftDerivs f [A] U := by
  have hh := (left_has A (l:=[]) (by simp) h).cexp
  simp only [leftDerivs,zero_smul,Work.G07.at_zero_increment] at hh
  exact ⟨hh.deriv,(hh.sub_const 1).deriv⟩

private lemma all_bounds {q : Directions G n → Prop} {c : ℝ} (k : ℕ) (h : Chart k f U) (hh : c ≤ 1)
    (hc : ∀ l : List _, l.length ≤ k → (∀ A∈l,q A) → ‖leftDerivs f l U‖ ≤ c) :
    ∀ l : List _, l.length ≤ k → (∀ A∈l,q A) → ‖leftDerivs (Complex.exp ∘ f) l U‖ ≤ mayerCost k ∧
      ‖leftDerivs (mayer f) l U‖ ≤ mayerCost k * c := by
  have he : ‖f U‖ ≤ c := hc [] (Nat.zero_le _) (by simp)
  have h0 := (norm_nonneg _).trans he
  have hz := Complex.norm_exp_sub_one_le (he.trans hh)
  have h_nil (k : ℕ) : ‖leftDerivs (Complex.exp ∘ f) [] U‖ ≤ mayerCost k ∧ ‖leftDerivs (mayer f) [] U‖ ≤ mayerCost k * c := by
    have ht := mayerCost_three_le k
    have hu := norm_add_le (mayer f U) 1
    simp only [mayer,sub_add_cancel,norm_one] at hu
    exact ⟨by change ‖Complex.exp (f U)‖ ≤ _; linarith,hz.trans (mul_le_mul (by linarith) he (norm_nonneg _) (by linarith))⟩
  intro l hl hD
  induction k generalizing l with
  | zero => rw [show l = [] from List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)]; exact h_nil 0
  | succ k ih =>
    induction l using List.reverseRecOn with
    | nil => exact h_nil (k+1)
    | append_singleton l A _ =>
      simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_le_add_iff_right] at hl
      have h' : Chart k f U := h.of_le (Nat.cast_le.mpr k.le_succ)
      let g := (Complex.exp ∘ f) * leftDerivs f [A]
      have hd : Chart k (Complex.exp ∘ f) U := h'.cexp
      have H := left_mul_bound hd (leftDerivs_chart [A] k (Nat.add_comm 1 k ▸ h))
        (fun l hl hy => (ih h' (fun l hl' => hc l (hl'.trans k.le_succ)) l hl hy).1) (fun l hl hy => by
          rw [← Work.G07.left_append]; exact hc _ (by simp [hl]) (by intro v hv; rcases List.mem_append.mp hv with ht|ht; exact hy _ ht; exact hD v (List.mem_append_right _ ht))) l hl
        (fun a ha => hD _ (by simp [ha]))
      have hK := mayerCost_three_le k
      have hN : ‖leftDerivs g l U‖ ≤ mayerCost (k+1)*c := H.trans ((mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl)
        (by positivity : 0 ≤ mayerCost k*c)).trans_eq (by rw [mayerCost,mul_assoc]))
      simp only [Work.G07.left_append]
      have h' : ∀ᶠ x in 𝓝 (0 : Directions G n), Chart (k+1) f (increment U x) :=
        chart_eventually (by rwa [Work.G07.at_zero_increment]) (fun i => by
          simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt)
      have hx := h'.mono fun x hx => heads (hx.of_le (Nat.cast_le.mpr (Nat.le_add_left 1 k))) A
      rw [left_congr (f:=leftDerivs (Complex.exp ∘ f) [A]) l U (g:=g) (hx.mono fun x hx => hx.1), left_congr (f:=leftDerivs (mayer f) [A]) l U (g:=g) (hx.mono fun x hx => hx.2)]
      exact ⟨hN.trans (mul_le_of_le_one_right (by linarith [mayerCost_three_le (k+1)]) hh),hN⟩
end Jets

section Regular
variable {B : BudgetPoint} {f : Config G n → ℂ} {X : Support n}

theorem mayer_regular (h : B.Regular X f) : B.Regular X (mayer f) := by
  have he U (hU : Healthy B.threshold X U) : Chart B.order (mayer f) U :=
    ((h.smooth U hU).cexp).sub contDiffAt_const
  exact ⟨fun _ _ hh => by unfold mayer; rw [h.sites _ _ hh], (Complex.continuous_exp.measurable.comp h.borel).sub measurable_const,
    fun k U => by unfold mayer; rw [h.symmetry k U], he,fun U hU A _ hl => left_has A hl (he U hU)⟩

theorem mayer_bound {o c} (h : B.Regular X f) (hh : B.supBounds o X f c) (he : c ≤ 1) :
    B.supBounds o X (mayer f) (mayerCost B.order*c) := ⟨mul_nonneg (by linarith [mayerCost_three_le B.order]) hh.1,
      fun U hU l hl hd => (all_bounds B.order (h.smooth U hU) he (hh.2 U hU) l hl hd).2⟩

theorem mayer_mask (t : ℝ) (X : Support n) (f : Config G n → ℂ) : mayer (masked t X f) = masked t X (mayer f) := by
  funext V; by_cases h : Healthy t X V
  · rw [masked_eq _ _ _ _ h]; simp only [mayer,masked_eq _ _ _ _ h]
  rw [masked_ne _ _ _ _ h]; simp only [mayer,masked_ne _ _ _ _ h,Complex.exp_zero, sub_self]
end Regular
end YM.Planned.Forced
