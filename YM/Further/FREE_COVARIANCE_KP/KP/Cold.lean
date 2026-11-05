import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import YM.Further.FREE_COVARIANCE_KP.KP.Weight


/-! # Smooth partition in radians & the low Gaussian -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι : Type*} {k l : ℤ} {f : ι → E4→ℂ} {Z : ℝ}

/-- Need far outside any disk of radius ≥1 -/
def rim (Z : ℝ) (h : 0<Z) : Window where
  look := {p : E4| Z<‖p‖}
  ok := isOpen_lt continuous_const continuous_norm
  hole hm := by have he : Z < ‖(0:E4)‖ := hm; rw [norm_zero] at he; linarith
lemma rim_weaker (hb : 1≤Z) (hg : 0<Z) (hl : Weight (rim Z hg) l f) (h : l≤k) : Weight (rim Z hg) k f := by
  refine ⟨hl.smooth,fun n => ?_⟩; obtain ⟨C,hC,H⟩ := hl.quotes n; refine ⟨C,hC,fun i p hp => ?_⟩
  apply (H i p hp).trans; exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (hb.trans (show Z<_ from hp).le) (by omega)) hC

def polar (b : ℝ) (p : E4) : ℝ := Real.exp (-(b*‖p‖^2))
def breeze (b : ℝ) (p : E4) : ℂ := ↑(polar b p)
lemma polar_smooth (b) {n : ℕ∞ω} : ContDiff ℝ n (polar b) := Real.contDiff_exp.comp ((contDiff_const.mul (contDiff_norm_sq ℝ)).neg)
lemma breeze_smooth (b) {n : ℕ∞ω} : ContDiff ℝ n (breeze b) := Complex.ofRealCLM.contDiff.comp (polar_smooth b)

private lemma reach (hb : 1≤Z) {b : ℝ} (hv : 0<b) (n k : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ p:E4,Z<‖p‖ → ‖iteratedFDeriv ℝ n (polar b) p‖ ≤ C* (‖p‖^k)⁻¹ := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    cases n with
    | zero =>
      cases k with
      | zero =>
        refine ⟨1,zero_le_one,fun p hp => ?_⟩
        have he : polar b p ≤1 := Real.exp_le_one_iff.mpr (by first | positivity | linarith [mul_nonneg hv.le (sq_nonneg ‖p‖)])
        rw [norm_iteratedFDeriv_zero]; simpa [abs_of_nonneg (show 0≤polar b p from (Real.exp_pos _).le)] using he
      | succ k =>
        let a : ℝ := b / (↑(k+1:ℕ):ℝ)
        have ha : 0<a := by unfold a; positivity
        refine ⟨a⁻¹ ^(k+1),by positivity,fun p hp => ?_⟩; let r := ‖p‖
        have hh : 1≤r := hb.trans hp.le; have hr : 0<r := zero_lt_one.trans_le hh
        have he : r≤a⁻¹*Real.exp (a*r^2) := by
          rw [mul_comm,← div_eq_mul_inv,le_div_iff₀ ha]
          apply le_trans ?_ (Real.add_one_le_exp _)
          rw [mul_comm]
          exact le_trans (by gcongr; nlinarith : a*r ≤ a*r^2) (by linarith)
        have h : r^(k+1) ≤ a⁻¹^(k+1)*Real.exp (b*r^2) := by
          convert! (pow_le_pow_left₀ hr.le he (k+1)) using 1; rw [mul_pow,← Real.exp_nat_mul]; congr 2; unfold a; field_simp
        rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs, polar,abs_of_pos (Real.exp_pos _),Real.exp_neg]; change _ ≤ _*(r^(k+1))⁻¹
        rw [← div_eq_mul_inv,le_div_iff₀ (by positivity : 0<r^(k+1)), mul_comm,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)]; exact h
    | succ n =>
      let L : E4 →L[ℝ] E4 →L[ℝ] ℝ := (-2*b) • (innerSL ℝ)
      have hg : fderiv ℝ (polar b)=fun p => polar b p • L p := by
        funext p
        have h := (((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_mul b).neg).exp
        rw [show (fderiv ℝ (polar b) p)=_ from h.fderiv]; ext v; simp [polar,L]; ring_nf; rfl
      have hl : ContDiff ℝ n L := L.contDiff
      have hu (p:E4) (hp : Z<‖p‖) (m) : ‖iteratedFDeriv ℝ m L p‖ ≤ ‖L‖*‖p‖ := by
        rcases m with _|m
        · rw [norm_iteratedFDeriv_zero]; exact L.le_opNorm _
        rw [← norm_iteratedFDeriv_fderiv,show fderiv ℝ L=fun _ => L from funext fun _ => L.fderiv]
        cases m
        · rw [norm_iteratedFDeriv_zero]; exact le_mul_of_one_le_right (norm_nonneg L) (hb.trans hp.le)
        rw [iteratedFDeriv_succ_const]; simp; positivity
      choose C hC H using fun i : Fin (n+1) => ih i.val i.isLt (k+1)
      let A := ∑ i : Fin (n+1), C i; have hA : 0≤A := Finset.sum_nonneg (fun _ _ => hC _)
      have he (j : ℕ) (hj : j<n+1) (p:E4) (hp : Z<‖p‖) : ‖iteratedFDeriv ℝ j (polar b) p‖ ≤ A * (‖p‖^(k+1))⁻¹ := by
        apply (H ⟨j,hj⟩ p hp).trans; gcongr; exact Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _)
      refine ⟨(∑ j∈Finset.range (n+1), (n.choose j:ℝ)*A*‖L‖), Finset.sum_nonneg (fun i _=> by positivity),fun p hp => ?_⟩
      have hr := (zero_lt_one.trans_le hb).trans hp
      rw [← norm_iteratedFDeriv_fderiv,hg]
      apply (norm_iteratedFDeriv_smul_le (polar_smooth _) hl p le_rfl).trans
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      calc
        _ ≤ ((n.choose i:ℝ) * (A*(‖p‖^(k+1))⁻¹)) * (‖L‖*‖p‖) := by gcongr; exacts [he i (Finset.mem_range.mp hi) p hp,hu p hp _]
        _ = _ := by field_simp; ring

lemma negative_quote (k : ℕ) (hb : 1≤Z) (ha : 0<Z) {b : ℝ} (hc : 0<b) : Weight (rim Z ha) (-(k:ℤ)) (fun (_:ι) => breeze b) := by
  let L := Complex.ofRealCLM
  refine ⟨fun _ => (breeze_smooth _).contDiffOn,fun n => ?_⟩
  obtain ⟨C,hC,H⟩ := reach hb hc n (k+n)
  refine ⟨‖L‖*C,by positivity,fun _ p hp => ?_⟩
  change ‖iteratedFDeriv ℝ n ((⇑L) ∘ polar b) p‖ ≤ _
  refine (L.norm_iteratedFDeriv_comp_left (polar_smooth b (n:=n)).contDiffAt le_rfl).trans ?_
  rw [show -(k:ℤ)-n =-((↑(k+n):ℤ)) by omega,zpow_neg, zpow_natCast,mul_assoc]; gcongr; exact H p hp
lemma far_fee (k : ℤ) (hb : 1≤Z) (ha : 0<Z) {b : ℝ} (hc : 0<b) : Weight (rim Z ha) k (fun (_:ι) => breeze b) :=
  rim_weaker hb ha (negative_quote k.natAbs hb ha hc) (by omega)
end YM.Further.FreeCovariance.KP
