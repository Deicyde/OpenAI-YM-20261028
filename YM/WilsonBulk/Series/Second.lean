import YM.WilsonBulk.Slice.Siding
import YM.Work.F03.Calculus
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Confirm first nontrivial check under chart scale: entire flat force

Extract via second coefficient criterion from local origin C² limit on rays.
Includes actual factorials, not assuming R approx polynomial limit arbitrary.
Use for actual tag polynomial and top Wilson. Separate dual statement for
later TP resetting.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology ContDiff Classical BigOperators
open Function Finset
open PowerSeries Filter
variable {α : Type} [Fintype α] {m : ℕ} {f : Tabletop α→ℝ}
lemma ink_eval (f : Tabletop α→ℝ) (x : Tabletop α) (n : ℕ) : MvPolynomial.eval x (PowerSeries.coeff n (ink f)) = (n.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ n f 0 (Function.const _ x) := by
  rw [ink_power,script_dual]; let F := (iteratedFDeriv ℝ n f 0).toMultilinearMap
  change _= _ • F _
  have hh : F (Function.const _ x)=∑ v:Legs α n,(∏ i,x (v i)) • F (spike ∘ v) := by
    rw [show Function.const (Fin n) x=fun i=>∑ j:α,x j • spike j from funext fun _=> spike_all x, MultilinearMap.map_sum]; refine sum_congr rfl fun i _=> ?_; exact MultilinearMap.map_smul_univ F _ _ -- check
  rw [hh,Finset.smul_sum]; refine sum_congr rfl fun v _=>?_; unfold photo; simp only [show F (spike ∘ v)=iteratedFDeriv ℝ n f 0 (spike ∘ v) from rfl, smul_eq_mul]; ring
lemma grade_eval2 (f : Tabletop α→ℝ) (x : Tabletop α) : MvPolynomial.eval x (coeff 2 (ink f)) = iteratedFDeriv ℝ 2 f 0 ![x,x]/2 := by rw [ink_eval,show Function.const (Fin 2) x=![x,x] from funext fun i=>by fin_cases i <;> rfl]; simp [Nat.factorial]; ring -- inspect
-- given diagonal limit to any polynomial p; no separate global uniformity
lemma ink_floor (hf : ContDiffAt ℝ ω f 0) (p : Formula α) (he : ∀ x:Tabletop α,Tendsto (fun t:ℝ=>f (t • x)/t^2) (𝓝[≠] 0) (𝓝 (MvPolynomial.eval x p))) : f 0=0 ∧ fderiv ℝ f 0=0 ∧ coeff 0 (ink f)=0 ∧ coeff 1 (ink f)=0 ∧ coeff 2 (ink f)=p := by
  let g x:=fun t:ℝ=>f (t • x)
  have hh (x : Tabletop α) : ContDiffAt ℝ 2 (g x) 0 := (show ContDiffAt ℝ 2 f ((0:ℝ) • x) by rw [zero_smul]; exact hf.of_le le_top).comp (f:=fun t:ℝ=> t • x) 0 (by fun_prop)
  have hz (x : Tabletop α):= Work.F03.value_slope_of_sq_limit (hh x).continuousAt (he x)
  have h₁ : f 0=0:= by simpa [g] using (hz 0).1
  have h₂ : fderiv ℝ f 0=0:= ContinuousLinearMap.ext fun x=> (Push.side f (hf.differentiableAt (by simp)) x).unique (hz x).2
  refine ⟨h₁,h₂,by simp only [coeff_zero_eq_constantCoeff,ink_norm,h₁,map_zero],?_ ,?_⟩
  · rw [ink_grade1 hf]; simp only [leafD,Analysis.D,h₂,_root_.zero_apply,map_zero,zero_mul,sum_const_zero]
  apply MvPolynomial.funext; intro x; rw [grade_eval2]
  have e := Work.F03.line_second (hf.of_le (m:=2) le_top) h₂ x
  rw [← e]; exact tendsto_nhds_unique (Work.F03.taylor_limit_two (hh x) (hz x).1 (hz x).2.deriv) (he x)
end YM.WilsonBulk.Sheet
