import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Laplace
import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Moment

/-!
# Trace-priced weighted tails on a local Gaussian change

Not allowing the same tiny potential cost independently at every site for free!
Pay the sum of all weights (trace of the counting-space diagonal), and compare
*normalized* expectations. The core can use a different covariance and shift
and needn't satisfy a weighted smallness hypothesis, only the p test and
locality, as above. No changes of interacting potential. The weight is allowed
to live on a larger set than the patch or even on the entire ambient counting
space. Finite-index theorems; to use uniformly, supply uniform trace (e.g.
summable radial weight from the patch) and other indicated bounds, note in
particular the cost of the posterior shift.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianInsertion

open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
open Multi.Vacuum (Gauss.pay)
open scoped Topology BigOperators Classical ENNReal

/-- Avoid an unnormalized assumption on the determinant when making a
weighted-tail estimate. -/
private lemma inverse_estimate {X : Type} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f)
    (h1 : Integrable (fun x => Real.exp (f x)) μ)
    (h2 : Integrable (fun x => Real.exp (-(f x))) μ) :
    1 ≤ (∫ x, Real.exp (f x) ∂μ) * (∫ x, Real.exp (-(f x)) ∂μ) := by
  let F (x : X) := Real.exp (f x/2)
  let G (x : X) := Real.exp ((-f x)/2)
  have hF (x : X) : F x ^ 2 = Real.exp (f x) := by
    rw [sq]; unfold F; rw [← Real.exp_add]; ring_nf
  have hG (x : X) : G x ^ 2 = Real.exp (-f x) := by
    rw [sq]; unfold G; rw [← Real.exp_add]; ring_nf
  have he : MemLp F 2 μ := (memLp_two_iff_integrable_sq (by
    unfold F
    exact (Real.continuous_exp.measurable.comp (hf.div_const _)).aestronglyMeasurable)).2 (by
      simp_rw [hF]; exact h1)
  have hg : MemLp G 2 μ := (memLp_two_iff_integrable_sq (by
    unfold G
    exact (Real.continuous_exp.measurable.comp (hf.neg.div_const _)).aestronglyMeasurable)).2 (by
      simp_rw [hG]; exact h2)
  let m := ∫ x, Real.exp (f x) ∂μ
  let n := ∫ x, Real.exp (-(f x)) ∂μ
  have hxy : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hxy
    (show (0 : X → ℝ) ≤ᵐ[μ] F from Eventually.of_forall fun x => (Real.exp_pos _).le)
    (show (0 : X → ℝ) ≤ᵐ[μ] G from Eventually.of_forall fun x => (Real.exp_pos _).le)
    (by simpa using he) (by simpa using hg)
  have ht (x : X) : F x * G x = 1 := by
    unfold F G; rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]
  have hb : 1 ≤ Real.sqrt m * Real.sqrt n := by
    simp_rw [ht, Real.rpow_two, hF, hG] at hh
    simpa [m,n, Real.sqrt_eq_rpow] using hh
  have hm : 0 ≤ m := integral_nonneg fun x => (Real.exp_pos _).le
  have hn : 0 ≤ n := integral_nonneg fun x => (Real.exp_pos _).le
  have hu := pow_le_pow_left₀ (by norm_num : 0 ≤ (1:ℝ)) hb 2
  rw [mul_pow, Real.sq_sqrt hm, Real.sq_sqrt hn, one_pow] at hu
  exact hu

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A C D : Gaussian.Table ι}
  {w z a d c : Vec ι} {p q K K' b : ℝ}

/-- Literal weighted condition on the *difference of potentials* (including
linear). Deliberately NOT on the determinant or additive normalizing constant. -/
def Weighted (A D : Gaussian.Table ι) (h w : Vec ι) (b : ℝ) : Prop :=
  ∀ z, |variation A D h z| ≤ b + Gauss.pay w z

lemma weighted_normalizer (hC : C.PosDef) (hD : D.PosDef) (ht : Ceiling D K) (hp : 0 ≤ K)
    (hw : ∀ i, 0 ≤ w i) (he : ∀ i, K*w i ≤ 1/4) (h : Weighted C D (d-c) w b) :
    likelihood C D c d d ≤ Real.exp (b+2*K*∑ i, w i) := by
  let T x := variation C D (d-c) (x-d)
  have hd x : T (d+x) = variation C D (d-c) x := by simp [T]
  have hm : Measurable T := (continuous_variation C D (d-c)).measurable.comp
    (measurable_id.sub measurable_const)
  obtain ⟨hl,-⟩ := laplace_price hD.posSemidef ht hp hw he hm d
    (fun x => show T (d+x) ≤ b + _ by rw [hd]; exact le_of_abs_le (h x))
  obtain ⟨hy,hz⟩ := laplace_price hD.posSemidef ht hp hw he hm.neg d
    (fun x => show -(T (d+x)) ≤ b + _ by rw [hd]; linarith only [(abs_le.mp (h x)).1])
  let L := likelihood C D c d d
  let U := ∫ x, Real.exp (T x) ∂law D d
  let V := ∫ x, Real.exp (-(T x)) ∂law D d
  have hx : L * U = 1 := calc
    _ = ∫ x, L * Real.exp (T x) ∂law D d := (integral_const_mul _ _).symm
    _ = ∫ x, likelihood C D c d x ∂law D d :=
      integral_congr_ae (Eventually.of_forall fun x => (likelihood_around x).symm)
    _ = 1 := (likelihood_integral hC hD).2
  have h1 : 1 ≤ U*V := inverse_estimate hm hl hy
  have h2 : 0 ≤ L := (likelihood_pos hC hD ..).le
  apply le_trans (b:=V) _ hz
  change L ≤ _
  calc
    L ≤ L*(U*V) := le_mul_of_one_le_right h2 h1
    _ = V := by rw [← mul_assoc, hx, one_mul]

/-- Sharper when no second core is needed: bound a weighted change on its
originating law. -/
theorem weighted (hA : A.PosDef) (hD : D.PosDef) (ht : Ceiling D K) (hK : 0 ≤ K)
    (hp : 1 ≤ p) (hw : ∀ i, 0 ≤ w i) (he : ∀ i, K*(p*w i) ≤ 1/4) (h : Weighted A D (d-a) w b) :
    (mixed A D p).PosDef ∧ moment A D p (d-a) ≤ Real.exp (2*p*(b + 2*K*∑ i, w i)) := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  let U := p • w
  have hu i : 0 ≤ U i := mul_nonneg hp'.le (hw i)
  let T x := variation A D (d-a) (x-d)
  have hd x : T (d+x) = variation A D (d-a) x := by simp [T]
  have hm : Measurable T := (continuous_variation A D (d-a)).measurable.comp
    (measurable_id.sub measurable_const)
  obtain ⟨hi,hx⟩ := laplace_price hD.posSemidef ht hK hu he (hm.const_mul p) d
    (show ∀ z, p*T (d+z) ≤ p*b + Gauss.pay U z from fun z => by
      rw [hd, pay_scale]
      exact (mul_le_mul_of_nonneg_left (le_of_abs_le (h z)) hp'.le).trans_eq (mul_add ..))
  have hg i : K * w i ≤ 1/4 :=
    (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hw i) hp) hK).trans (he i)
  let L := likelihood A D a d d
  let c := b + 2*K*∑ i,w i
  have hL : 0 < L := likelihood_pos hA hD ..
  have hr : L ^ p ≤ Real.exp (c*p) := by
    rw [Real.exp_mul]; exact Real.rpow_le_rpow hL.le (weighted_normalizer hA hD ht hK hw hg h) hp'.le
  have hy (x : Vec ι) : likelihood A D a d x ^ p = L ^ p * Real.exp (p*T x) := by
    rw [likelihood_around]
    change (L * Real.exp (T x))^p = _
    rw [Real.mul_rpow hL.le (Real.exp_pos _).le, mul_comm p, Real.exp_mul]
  have hl : (mixed A D p).PosDef := (power_iff hA hD).mp (show
      Integrable (fun x => likelihood A D a d x ^ p) (law D d) by
    simp_rw [hy]; exact hi.const_mul _)
  refine ⟨hl,?_⟩
  rw [← (power_integral hA hD hl a d).2]
  simp_rw [hy]; rw [integral_const_mul]
  calc
    _ ≤ Real.exp (c*p) * Real.exp (p*b + 2*K*∑ i,U i) := mul_le_mul hr hx
      (integral_nonneg fun x => (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; unfold U c; simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring_nf

section WithCore



variable {S : Finset ι}



variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {F : Vec ι → X}



end WithCore
end YM.SectorTools.PhysicalGaussianInsertion
