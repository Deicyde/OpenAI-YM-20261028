import YM.RG08.Origin.Scroll

/-! # Formal exponential of positive-grade action series

Smooth pointwise coefficients (no coupling or thermodynamic domain).
Preserves time-charge support control. Formal differentiation along g uses
all lower grade inputs only, constant 1 at tau^0 grade 0. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Finset Filter Analysis
open scoped Topology ContDiff
variable {X : Type}

-- specialized real tutors: presence of rational factorials

def ingr (n : ℕ) (R : Type) [One R] [Zero R] : R := if n=0 then 1 else 0

def priori (F : Scroll (Psalm X)) (n e : ℕ) : Psalm X := match e with
    | 0 => ingr n _
    | e+1 => ((↑(e+1 : ℕ)):ℝ)⁻¹ • ∑ b∈wheel n,
          ∑ a : {p : ℕ×ℕ // p∈wheel (e+1)}, if a.val.1=0 then 0 else
            countG F b.1 a.val.1 * priori F b.2 a.val.2
termination_by e
decreasing_by have h := mem_antidiagonal.mp a.property; omega

variable {F : Scroll (Psalm X)}
lemma priori_zero (n) : priori F n 0=ingr n _ := by rw [priori]
lemma priori_succ (n e) : priori F n (e+1)= (↑(e+1:ℕ):ℝ)⁻¹ • dancing (countG F) (priori F) n (e+1) := by
  rw [priori,dancing]; congr 1; refine sum_congr rfl fun b _=>?_ ;
  rw [← Finset.sum_coe_sort (wheel (e+1)) (fun a=> _ * _)] -- explicit
  apply sum_congr rfl; intro a _; split; next h => rw [h, muted_counts F b.1,zero_mul]
  next h => rfl

def Rhythm (R : Type) [CommSemiring R] (F S : Scroll R) := (∀ n,F n 0=ingr n _) ∧ countG F=dancing (countG S) F
lemma rhythm_exp (F : Scroll (Psalm X)) : Rhythm _ (priori F) F := by
  refine ⟨priori_zero,?_⟩; funext n e; cases e with
  | zero => rw [dance_left_muted _ _ (muted_counts _) n]; exact muted_counts _ n
  | succ k => rw [countG,priori_succ, ← Nat.cast_smul_eq_nsmul ℝ,smul_inv_smul₀]; positivity
lemma rhythm_unique {x : Scroll (Psalm X)} (h : Rhythm _ x F) : x=priori F := by
  funext n e
  induction e using Nat.caseStrongRecOn generalizing n with
  | zero => rw [h.1 n,priori_zero]
  | ind e he =>
    apply smul_right_injective _ (show ((↑(e+1 : ℕ)):ℝ)≠0 by positivity)
    dsimp only
    rw [Nat.cast_smul_eq_nsmul,Nat.cast_smul_eq_nsmul]; change countG x n (e+1)= countG (priori F) n (e+1); rw [h.2,(rhythm_exp F).2]
    exact dance_quiet _ _ _ (muted_counts _) (fun i hi j=>he i (Nat.lt_succ_iff.mp hi) j) _
lemma priori_timing (h : tempered _ F) : tempered _ (priori F) := by
  intro i n; induction n using Nat.caseStrongRecOn generalizing i with
  | zero => intro he; unfold terrace at he; rw [priori_zero,ingr,if_neg]; omega
  | ind n ih =>
    intro he; rw [priori_succ]; refine Eq.trans (congr_arg _ (sum_eq_zero (s:=wheel i) (f:=fun b=> ∑ a ∈ wheel (n+1), countG F b.1 a.1 * priori F b.2 a.2) (fun b hb=>sum_eq_zero ?_))) (smul_zero _)
    intro a ha; have hh := mem_antidiagonal.mp ha; have hp := mem_antidiagonal.mp hb
    by_cases hu : a.1=0; · rw [countG,hu,zero_smul,zero_mul]
    by_cases hh : terrace a.1 < b.1
    · rw [countG,h _ _ hh, smul_zero,zero_mul]
    rw [ih a.2 (by omega) b.2 (by unfold terrace at *; omega), mul_zero]

variable [Fintype X]
lemma priori_fluid (h : Fluid F) : Fluid (priori F) := by
  intro n e; induction e using Nat.caseStrongRecOn generalizing n with
  | zero => rw [priori_zero]; unfold ingr; split <;> exact contDiff_const
  | ind e he =>
    have hs {ι : Type} (p : Finset ι) {f : ι → Psalm X} (hf : ∀ i∈p,ContDiff ℝ ω (f i)) : ContDiff ℝ ω (∑ i∈p,f i) := by rw [show (∑ i∈p, f i)=(fun v=>∑ i∈p, f i v) from funext fun v=>Finset.sum_apply v ..]; exact ContDiff.sum hf
    rw [priori_succ,dancing]; refine ContDiff.const_smul (↑(e+1:ℕ):ℝ)⁻¹ (hs (wheel n) (f:=fun b=> ∑ a∈wheel (e+1), countG F b.1 a.1 * priori F b.2 a.2) (fun i hi=> hs (wheel (e+1)) (fun b hb=> ?_)))
    have hp := mem_antidiagonal.mp hb
    by_cases hh : b.1=0; · rw [hh,muted_counts _ i.1,zero_mul]; exact contDiff_const
    apply ContDiff.mul _ (he b.2 (by omega) i.2); unfold countG; rw [← Nat.cast_smul_eq_nsmul ℝ]; exact ContDiff.const_smul (↑b.1:ℝ) (h i.1 _)
end YM.RG08
