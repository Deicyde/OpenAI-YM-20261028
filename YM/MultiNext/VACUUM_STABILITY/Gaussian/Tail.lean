import YM.MultiNext.VACUUM_STABILITY.Gaussian.Laplace
import YM.MultiNext.VACUUM_STABILITY.Sums


set_option warningAsError false

/-!
# One conditional Gaussian score

At fluctuation calculation at one U, even with a change back from held coordinates (if
producer proves the density and score rewrite). No unrequested asymptotic. Retain all
trigger sites in counted S, not trying to earn a share from expecting a distinct physical
trigger per letter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Gauss
open Filter Finset Function MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Classical

variable {I J : Type} [Fintype I] [Fintype J]

-- costs nonlinear-power independent of dim of original standard Gaussian

def coin (K : ℝ) := (16*(K+1))⁻¹
def rim (I : Type) [Fintype I] (K : ℝ) := coin K/(1+Fintype.card I)

lemma coin_ok {K : ℝ} (h : 0≤K) : 0 < coin K ∧ K*coin K ≤ 1/16 := by
  have he : 0 < 16*(K+1) := by linarith
  refine ⟨inv_pos.mpr he,?_⟩
  unfold coin; rw [←div_eq_mul_inv, div_le_iff₀ he]; linarith

lemma rim_ok {K : ℝ} (h : 0≤K) : 0 < rim I K ∧ (1+Fintype.card I)*rim I K=coin K := by
  have hh := (coin_ok h).1
  have hu : (0:ℝ) < 1+Fintype.card I := by positivity
  unfold rim; exact ⟨div_pos hh hu, by field_simp⟩

lemma rim_le {K : ℝ} (h : 0 ≤ K) : rim I K ≤ coin K := div_le_self (coin_ok h).1.le (by simp)

private lemma overhead {a b : ℝ} (h : 0 < a) (hh : 0 ≤ b) (p : ℕ) : b^p ≤ (p.factorial/a^p)*Real.exp (a*b) := by
  let k := Absolute.rexp (a*b) (mul_nonneg h.le hh)
  have he := Absolute.little k p
  rw [inv_mul_le_iff₀] at he
  · rw [mul_pow] at he; rw [div_mul_eq_mul_div]; apply (le_div_iff₀ (pow_pos h _)).2; rwa [mul_comm (b^p)]
  positivity

-- final exponential cost written using sums of selected budgets

def quota (K r : ℝ) (N k : ℕ) (W : ℝ) (L : ℕ) (b : ℝ) :=
    -- here r=coin/(1+N). cost capped in N through r. N separate readability
    (k.factorial/r^k)*Real.exp (r - coin K*b + 2*K*(W+L*coin K+N*r))

/-- `cost` on the SAME kernel; S subset of chosen Z positions where need large event
(count even color components separately). Signature nonlinear weight may accumulate over many
letters if one `w` can price them. Uses true full conditional dimension L in the ONE polynomial
only. -/
theorem score (q : I → J → ℝ) {K : ℝ} (h : adjBound q K) (hK : 0 ≤ K)
    (w : Row I) (hw : ∀ i,0 ≤ w i) (he : ∀ i,K*w i ≤ 1/8) (k : ℕ) (S : Finset I)
    (c b W : ℝ) {E : Type*} [NormedAddCommGroup E]
    (F : Row J → E) (hm : AEStronglyMeasurable F (standard J)) (hc : 0≤c) (hW : ∑ i,w i ≤ W)
    (hn : ∀ᵐ y ∂standard J, F y ≠ 0 →
      let z := mapRows q y
      ‖F y‖ ≤ c*(1+squares z)^k * Real.exp (pay w z) ∧ b ≤ ∑ i∈S,z i ^2) :
    Integrable F (standard J) ∧ (∫ y, ‖F y‖ ∂standard J) ≤ c * quota K (rim I K) (Fintype.card I) k W S.card b := by
  let t:=coin K; let r:=rim I K
  have ht := coin_ok hK
  have hu : 0 < r := (rim_ok hK).1; have hr : r ≤ t := rim_le hK; change 0<t∧_ at ht
  let w' i := w i+r+(if i∈S then t else 0)
  have hQ i : 0 ≤ w' i := add_nonneg (add_nonneg (hw i) hu.le) (ite_nonneg ht.1.le le_rfl)
  have hy i : K*w' i ≤ 1/4 := by
    rw [show K*w' i = K*w i+K*r+K*(if i∈S then t else 0) by unfold w'; ring]
    have hb:=le_trans (mul_le_mul_of_nonneg_left hr hK) ht.2
    have hg := he i; obtain ⟨-,H⟩ := ht; change K*t ≤ _ at H; split <;> linarith
  let f (y : Row J) := Real.exp (pay w' (mapRows q y))
  obtain ⟨hf,hF⟩:=conditional q K h hK w' hQ hy
  let A := c*(k.factorial/r^k)*Real.exp (r-t*b)
  have ha : 0≤A := by unfold A; positivity
  have hE (z : Row I) : pay w' z = pay w z+r*squares z+t*∑ i∈S,z i^2 := by
    unfold w' pay squares
    simp_rw [add_mul,Finset.sum_add_distrib,Finset.mul_sum, ite_mul,zero_mul]
    rw [Finset.sum_ite_mem, univ_inter]
  have hg : ∀ᵐ y ∂standard J, ‖F y‖ ≤ A*f y := by
    filter_upwards [hn] with y h; by_cases H : F y=0
    · rw [H,norm_zero]; exact mul_nonneg ha (Real.exp_pos _).le
    obtain ⟨hx,hy⟩:= h H; let z:=mapRows q y
    have hl : 0≤squares z := Finset.sum_nonneg fun i _ => sq_nonneg _
    refine hx.trans ?_
    calc
      _ ≤ c*((k.factorial/r^k)*Real.exp (r*(1+squares z))) * Real.exp (pay w z) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (overhead hu (by linarith) _) hc) (Real.exp_pos _).le
      _ = c*(k.factorial/r^k)* Real.exp (r*(1+squares z)+pay w z) := by rw [Real.exp_add]; ring
      _ ≤ c*(k.factorial/r^k)* Real.exp ((r-t*b)+pay w' z) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (by positivity)
        have hz := mul_le_mul_of_nonneg_left (show b ≤ ∑ i∈S,z i^2 from hy) ht.1.le
        rw [hE]; linarith
      _ = _ := by unfold A f; rw [Real.exp_add]; ring
  have ht : Integrable (fun y => A*f y) (standard J) := hf.const_mul A
  have hx := ht.mono' hm hg
  refine ⟨hx, (integral_mono_ae hx.norm ht hg).trans ?_⟩
  rw [integral_const_mul]
  apply le_trans (mul_le_mul_of_nonneg_left hF ha)
  unfold A quota
  change c*(k.factorial/r^k)*_ * _ ≤ c*((k.factorial/r^k)*Real.exp (r-t*b+2*K*(W+S.card*t+Fintype.card I*r)))
  rw [mul_assoc _ (Real.exp _), ←Real.exp_add,←mul_assoc c]
  gcongr; rw [←Finset.mul_sum,←Finset.mul_sum,←mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold w'; rw [Finset.sum_add_distrib,Finset.sum_add_distrib]; simp only [Finset.sum_ite_mem,Finset.univ_inter,
    Finset.sum_const,card_univ,nsmul_eq_mul]; linarith
end YM.Multi.Vacuum.Gauss
