import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Corridor

/-!
# Complete forced words, 

Reprice after adding the negative copies of omitted full logarithm tuples (only for actual
hard-core contacts with the ORIGINAL seed family) and the discrepancies of the low indicator
moves. Uses only unmarked all-field values on the first integrated seeds and the SAME unforced
amplitudes as priced for the regular log. Guard eligibility matched exactly including equality.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open RG Wilson Lattice Filter Function Set Push.AbsoluteSums Trees Ursell Finset Further.LogJets
open scoped Classical Matrix.Norms.Frobenius Topology BigOperators

def Both (D c v w : ℝ) := |v| ≤ c ∧ |w| ≤ c ∧ |v-w| ≤ D*c
namespace Both
variable {D c v w : ℝ}




lemma zero (hD : 0 ≤ D) (hc : 0 ≤ c) : Both D c 0 0 := by simpa [Both, hc] using mul_nonneg hD hc
lemma swap (h : Both D c v w) : Both D c w v := ⟨h.2.1,h.1, (abs_sub_comm w v).trans_le h.2.2⟩







end Both



variable {G : Gauge} {n : Side} {ι κ H : Type*}
namespace Content
variable (f : Content G n ι κ H) (A : Placement G n ι κ) (p : BudgetPoint)

def mergeExponent := p.supportExponent+1+1


structure PairValues (v w : H) (b b' D g γ q u : ℝ) : Prop where
  seed : ∃ c : κ→ℝ, (∀ i U, Both D (Real.exp (-g)*c i) (f.forced b v i U) (f.forced b' w i U)) ∧
    Ac.Hit (fun i => (A.seed i).support) p.B c (mergeExponent p) u
  unmarked : ∃ c : ι→ℝ, Ready A.reads p.B (fun i => 2*c i) (mergeExponent p) γ 1 q ∧
    ∀ i U, Healthy p.threshold (A.reads i) U → Both D (c i) (f.unforced b v i U) (f.unforced b' w i U)
  changes : ∃ c : ℕ→ℝ, (∀ i,0 ≤ c i ∧ ∀ j U, ¬ Healthy p.threshold (A.attachment i) U → |f.move i j U| ≤ c i) ∧
    Ac.Hit A.attachment p.B c (mergeExponent p) u

variable {f A p} {v w : H} {b b' D g γ q u y : ℝ}

def quota (γ q : ℝ) := γ * (1-q)⁻¹
def mild (γ q u : ℝ) := quota γ q +16*u
def mergeHit (γ q u : ℝ) := 2*(u + Real.exp 1 * mild γ q u)

namespace PairValues
variable (he : PairValues f A p v w b b' D g γ q u) (hD : 0 ≤ D)
    (hy : 0 < y) (h₁ : b ∈ Set.Icc (y/2) (2*y)) (h₂ : b' ∈ Set.Icc (y/2) (2*y)) (hδ : |b-b'|/y ≤ D)
include he hD


include hy h₁ h₂ hδ in
lemma moves : ∃ c : ℕ → ℝ, Ac.Hit A.attachment p.B c (mergeExponent p) (16*u) ∧
    ∀ i U, Both D (c i) (f.correction A p y b i U) (f.correction A p y b' i U) := by
  obtain ⟨c,hc,h⟩ := he.changes
  have H (b : ℝ) (hh : b ∈ Set.Icc (y/2) (2*y)) : b/y ∈ Set.Icc (2:ℝ)⁻¹ 2 := ⟨(le_div_iff₀ hy).2 (by linarith [hh.1]),(div_le_iff₀ hy).2 hh.2⟩
  have hM (j : Grade) : |multiplier j (b/y)-multiplier j (b'/y)| ≤ D*4 := (multiplier_change _ (H _ h₁) (H _ h₂)).trans (mul_le_mul_of_nonneg_right
    (by rwa [← sub_div,abs_div,abs_of_pos hy]) (by norm_num))
  refine ⟨_,AnalyticBridge.VerifiedReset.Quotes.hit_scale (by norm_num : 0 ≤ (16:ℝ)) h,fun i U => ?_⟩
  have hc' := (hc i).1
  unfold correction; split; exact Both.zero hD (by positivity)
  next hi =>
    simp only [polynomial,Finset.sum_apply]
    have hv : ∀ b : ℝ, b∈Set.Icc (y/2) (2*y) → |∑ j, multiplier j (b/y)*f.move i j U| ≤ 16*c i := by
      intro b hh; refine (abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (g:=fun _=>4*c i) (fun j _ => ?_)).trans_eq ?_)
      · rw [abs_mul]; exact mul_le_mul (multiplier_bound _ (H _ hh)) ((hc i).2 j U hi) (abs_nonneg _) (by norm_num)
      change (∑ _ : Grade,_) = _; simp; ring
    refine ⟨hv _ h₁,hv _ h₂,?_⟩; rw [← sum_sub_distrib]; simp_rw [← sub_mul]
    exact (abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (g:=fun j => D*4*c i) fun j _ => by rw [abs_mul]; exact mul_le_mul (hM j) ((hc i).2 j U hi) (abs_nonneg _) (by positivity)).trans_eq
      (by change (∑ _ : Grade, _) = _; unfold Grade; simp; ring))

include hy h₁ h₂ hδ





omit hD hy h₁ h₂ hδ in
lemma budgets : 0 ≤ u ∧ 0 ≤ mergeHit γ q u := by
  obtain ⟨_,hc,H⟩ := he.unmarked; obtain ⟨_,_,hq⟩ := he.seed
  have hu := budget_nonneg (hq 0); refine ⟨hu,?_⟩
  have hg := hc.1; have ht := sub_pos.mpr hc.2.2.2.1
  unfold mergeHit mild quota; positivity


end PairValues
end Content
end YM.PhysicalNext.InterpolatedSecantsFc
