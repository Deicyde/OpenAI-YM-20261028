import YM.Pert.Lattice.Tamed
import Mathlib.Probability.Moments.MGFAnalytic
/-! Centered scalar Gaussian IBP recursion from the mgf. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Warp
open Function Filter Set MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

def ev (v x : ℝ) : ℝ := Real.exp (v*x^2/2)
@[fun_prop] lemma ev_cd (v : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (ev v) := by unfold ev; fun_prop
lemma ev_d (v : ℝ) : deriv (ev v) = fun x=> v*(x * ev v x) := by
  funext x;unfold ev; rw (occs:=.all) [_root_.deriv_exp (by fun_prop),deriv_div_const,deriv_const_mul_field]; simp <;> try fun_prop
  ring
lemma ev_next (v : ℝ) (n : ℕ) : iteratedDeriv (n+1) (ev v) 0 = (n:ℝ) * v * iteratedDeriv (n-1) (ev v) 0 := by
  have h := ((ev_cd v).of_le (show ((n:ℕ∞):WithTop ℕ∞) ≤ ((⊤:ℕ∞):WithTop ℕ∞) by norm_cast; exact le_top)).contDiffAt (x:=0)
  rw [iteratedDeriv_succ',ev_d,iteratedDeriv_const_mul_field v,iteratedDeriv_fun_mul (f:=fun t:ℝ=>t) (by fun_prop) h]
  simp only [iteratedDeriv_fun_id_zero]; by_cases hn : n=0;· subst n; simp [Finset.sum_range_one]
  rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr (by omega)) (fun d _ hd=> by simp [hd])];simp [mul_comm]; ring
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] (μ : Measure E) [OpensMeasurableSpace E] [IsGaussian μ]
lemma tilted (v : ℝ) : mgf (fun x:ℝ=>x) (gaussianReal 0 v.toNNReal) = ev (max v 0) := by
  rw [mgf_fun_id_gaussianReal]; simp [Real.coe_toNNReal']; rfl
lemma diagonal_walk (L : E→L[ℝ] ℝ) (hL : ∫ x, L x ∂μ = 0) (n : ℕ) : (∫ x, L x ^ (n+1) ∂μ) = (n:ℝ)*(∫ x,L x ^ 2 ∂μ) * (∫ x,L x ^ (n-1) ∂μ) := by
  let v := variance L μ
  have e : μ.map L = gaussianReal 0 v.toNNReal := by simpa only [hL,v] using @IsGaussian.map_eq_gaussianReal E _ _ _ _ μ _ L
  have ev0 : ev (max v 0) 0=1 := by simp [ev]
  have H (k : ℕ): ∫ x,L x ^ k ∂μ = iteratedDeriv k (ev (max v 0)) 0 := by
    rw [←tilted,iteratedDeriv_mgf_zero (by simp), ← e]
    convert! (integral_map (μ:=μ) (f:=fun x:ℝ => x^k) L.continuous.aemeasurable (by fun_prop)).symm -- name?
  have hx : iteratedDeriv 2 (ev (max v 0)) 0 = max v 0 := by simpa [ev0] using ev_next (max v 0) 1
  rw [H,ev_next]; simp only [H,hx]
end YM.Pert.Warp
