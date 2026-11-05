import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Price
import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Laplace
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Shift

/-!
# One joint exponential test

For both actual covariance marginals, with the actual normalized mean shift
on the nonflat one, earn the exponential (counting squared norm) price from
the covariance ceiling. Uses the accepted Laplace price with smallness
actually checked on *these tables*. This is a convenient uniform absolute
integrability tool, stronger than just buying high-order moments. It says
nothing about arbitrary exponentials on these marginals (esp. powers of a
likelihood without a tilted precision check).
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
open AnalyticBridge.LocalGaussianLaws
open SectorTools PhysicalGaussianInsertion
open SectorTools.PhysicalGaussianSwitch (shift)
open scoped Topology BigOperators

variable {I : Type} [Fintype I]
variable {K : ℕ} {E x : ℝ}

lemma continuous_energy : Continuous (Density.energy (n:=I)) := by
  unfold Density.energy dotProduct; fun_prop
lemma energy_nonneg (x : Vec I) : 0 ≤ Density.energy x := FreeResolvent.normSum_nn x

/-- Counting Euclidean norm too, as distinct from `Vec I`'s pi sup norm. -/
def countingNorm (x : Vec I) : ℝ := Real.sqrt (Density.energy x)

lemma countingNorm_nonneg (x : Vec I) : 0 ≤ countingNorm x := Real.sqrt_nonneg _
lemma countingNorm_squared (x : Vec I) : countingNorm x ^ 2 = Density.energy x :=
  Real.sq_sqrt (energy_nonneg x)
lemma continuous_countingNorm : Continuous (countingNorm (I:=I)) := continuous_energy.sqrt
lemma norm_le_countingNorm (x : Vec I) : ‖x‖ ≤ countingNorm x := by
  apply (pi_norm_le_iff_of_nonneg (countingNorm_nonneg x)).mpr
  intro i
  apply (Real.le_sqrt (norm_nonneg _) (energy_nonneg x)).mpr
  rw [Real.norm_eq_abs, sq_abs]; exact FreeResolvent.le_normSum x i
lemma energy_bound (z : Vec I) {M : ℝ} (h : ‖z‖ ≤ M) (hK : Fintype.card I ≤ K) :
    Density.energy z ≤ (K:ℝ) * M^2 := by
  have hi (i : I) : |z i| ≤ M := by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm z i).trans h
  unfold Density.energy dotProduct
  calc
    _ ≤ ∑ _i : I, M^2 := Finset.sum_le_sum (fun i _ => by
      rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hi i) _)
    _ = (Fintype.card I:ℝ)*M^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK) (sq_nonneg _)

/-- Use constant weight in the counting `pay` currency. -/
lemma pay_const (z : Vec I) (h : ℝ) : Multi.Vacuum.Gauss.pay (fun _ => h) z = h * Density.energy z := by
  unfold Multi.Vacuum.Gauss.pay Density.energy dotProduct; rw [Finset.mul_sum]; simp only [sq]

/-- Full exponential budget; `heat` already has the local-cardinality
price, independent of the degree (which will affect the coefficients
charged against this budget). -/
def kiln (K : ℕ) (E : ℝ) : ℝ :=
  let h := heat K E
  Real.exp (2*h*((K:ℝ)*(centerBill K E)^2) + 2*topBill K E*((K:ℝ)*(2*h)))
lemma kiln_pos (K : ℕ) (E : ℝ) : 0 < kiln K E := Real.exp_pos _

def fuel (t : ℝ) (z : Vec I) := Real.exp (t * Density.energy z)

lemma fuel_pos (t : ℝ) (z : Vec I) : 0 < fuel t z := Real.exp_pos _

structure Hot (K : ℕ) (E : ℝ) (μ : Measure (Vec I)) : Prop where
  paid : Integrable (fuel (heat K E)) μ
  cap : (∫ x, fuel (heat K E) x ∂μ) ≤ kiln K E

variable [DecidableEq I]
variable {C B : Gaussian.Table I} {δ : Vec I}

/-- Works for either covariance if the constant-weight exponential budget and
normalized mean pass. In the application, the bills are already *earned*.
Uses `laplace_price` at precision margin given by `Billed.tilt_gap`. -/
lemma shifted_heat (hE : 0 ≤ E) (hK : Fintype.card I ≤ K)
    (hC : C.PosDef) (he : Billed C E) (h : ‖δ‖ ≤ centerBill K E) :
    Hot K E (shift C δ) := by
  let r := heat K E
  let K₀ := topBill K E
  let b := 2*r*((K:ℝ)*(centerBill K E)^2)
  have hr : 0 < r := heat_pos K hE
  have hk : 0 < K₀ := topBill_pos K hE
  have hShift : ∀ z : Vec I, r*Density.energy (δ+z) ≤ b + Multi.Vacuum.Gauss.pay (fun _ => 2*r) z := by
    intro z
    rw [pay_const, ← pay_const (δ+z)]
    refine (pay_add_le (w:=fun _ : I => r) (fun _ => hr.le) z δ).trans ?_
    rw [pay_const, pay_const, ← mul_assoc, ← mul_assoc]
    exact add_le_add_left (mul_le_mul_of_nonneg_left (energy_bound δ h hK) (by positivity)) _
  have ht := laplace_price (K:=K₀) hC.posSemidef (he.ceiling hE hK) hk.le
    (w:=fun i => 2*r) (fun _ => by positivity) (fun _ => (heat_pays K hE).le)
    (continuous_energy.const_mul r).measurable δ hShift
  have hh := ht.2
  refine ⟨ht.1,hh.trans ?_⟩
  apply Real.exp_monotone
  change b + _ ≤ b + 2*K₀*((K:ℝ)*(2*r))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (Fintype.card I:ℝ) ≤ K := Nat.cast_le.mpr hK
  gcongr



end YM.PhysicalNext.WeightedGaussianMarginal45C
