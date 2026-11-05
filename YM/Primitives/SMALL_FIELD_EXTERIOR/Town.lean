import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Primitives.SMALL_FIELD_EXTERIOR.Normal

/-!
# Price with slow (& inverse) site weights

Reuse exponential tilt kernel comparisons (periodic separation, counting).
Combined with the variational estimate this controls spatial response when we can
supply stronger UNIFORM decay data than just a uniform scalar gap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter MeasureTheory Matrix
open Lattice
open scoped Topology BigOperators ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W f g : Points ι → ℝ} {C : Matrix ι ι ℝ}
    {n : Side} {l : ι → Site n} {r a b M m e k k' D : ℝ}

def slow (l : ι → Site n) (a : ℝ) (i : Site n) (j : ι) := Real.exp (a*separation i (l j))
omit [Fintype ι] [DecidableEq ι] in
lemma slow_pos (l : ι → Site n) (a : ℝ) (x : Site n) (i : ι) : 0 < slow l a x i := Real.exp_pos _
omit [Fintype ι] [DecidableEq ι] in
lemma costed (i : Site n) (a : ℝ) (H : Matrix ι ι ℝ) : conjugated (slow l a i) H= YM.Push.Uniform.tilt a l i H := by
  ext; simp [conjugated,YM.Push.Uniform.tilt, slow, mul_sub,Real.exp_sub]; ring



lemma chargeNorm_pay (hr : 0 < r) (hV : Regular r 2 V) (w : ι → ℝ) (hf : Regular r 1 f) (A : ι → ℝ)
    (hA : ∀ i x, x∈cube ι r → |w i * pc i f x| ≤ A i) :
    chargeNorm w r V f ≤ Real.sqrt (∑ i,A i^2) := by
  apply Real.sqrt_le_sqrt; apply Finset.sum_le_sum
  intro i _
  have hp := raw_one_pos hr hV.cOn
  unfold mean
  rw [← mul_div_assoc, div_le_iff₀ hp, ← raw_smul,← raw_smul]
  have hc := hf.tangent_continuous i
  have he : ContinuousOn (pc i f ^ 2) (cube ι r) := by rw [pow_two]; exact hc.mul hc
  refine raw_mono hV.cOn (continuousOn_const.smul he) (continuousOn_const.smul (show ContinuousOn (1:Points ι → ℝ) (cube ι r) from continuousOn_const)) (fun x hx => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one,pow_two (pc i f),Pi.mul_apply]
  rw [← sq,← mul_pow]; exact sq_le_sq.mpr ((hA i x hx).trans (le_abs_self _))

lemma chargeNorm_fewer (hr : 0 < r) (hV : Regular r 2 V) (w : ι → ℝ) (hf : Regular r 1 f) (S : Finset ι)
    (hA : ∀ i∈S, ∀ x∈cube ι r, |w i * pc i f x| ≤ b) (hb : 0 ≤ b)
    (hh : ∀ i∉S, ∀ x∈cube ι r, pc i f x=0) :
    chargeNorm w r V f ≤ Real.sqrt (S.card:ℝ)*b := by
  let g : ι → ℝ := fun i => if i∈S then b else 0
  have he i x (hx : x∈cube ι r) : |w i * pc i f x| ≤ g i := by
    by_cases hi : i∈S
    · simpa only [g,if_pos hi] using hA i hi x hx
    simp [g,hh i hi x hx,hi]
  apply (chargeNorm_pay hr hV w hf g he).trans_eq
  have hv : ∑ i : ι, g i ^2=S.card*b^2 := calc
    _ = ∑ i∈S, g i ^2 := (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simp [g,hi])).symm
    _ = ∑ _i∈S,b^2 := Finset.sum_congr rfl fun i hi => by simp [g,hi]
    _ = _ := by simp
  rw [hv, Real.sqrt_mul (by positivity),Real.sqrt_sq hb]

/-- Specify actual coordinate support charged (even if from a prior
calculation upstream, don't truncate it silently). Centers and radii
in four-dimensional periodic geometry. -/
structure Features (l : ι → Site n) (x : Site n) (R : ℕ) (S : Finset ι) (r : ℝ) (f : Points ι → ℝ) (k : ℝ) : Prop where
  reg : Regular r 1 f
  bound : 0 ≤ k
  within (i : ι) : i∈S → separation x (l i) ≤ R
  interior (i : ι) : i∈S → ∀ y∈cube ι r, |pc i f y| ≤ k
  exterior (i : ι) : i∉S → ∀ y∈cube ι r, pc i f y=0

def feat (e : ℝ) (S : Finset ι) (R : ℕ) (k : ℝ) := Real.sqrt (S.card:ℝ) * (Real.exp (e*R) * k)
variable {x y : Site n} {R R' : ℕ} {S T : Finset ι}
lemma Features.pay (hr : 0 < r) (hV : Regular r 2 V) (he : Features l x R S r f k) (hb : 0 ≤ b) :
    chargeNorm (slow l b x) r V f ≤ feat b S R k := by
  apply chargeNorm_fewer hr hV _ he.reg S _ (mul_nonneg (Real.exp_pos _).le he.bound) he.exterior
  intro i hi x hx; rw [abs_mul, abs_of_pos (slow_pos l b _ _)]
  exact mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast he.within i hi) hb))
    (he.interior i hi x hx) (abs_nonneg _) (Real.exp_pos _).le
lemma Features.gain (hr : 0 < r) (hV : Regular r 2 V) (he : Features l y R S r f k) (x : Site n) (hb : 0 ≤ b) :
    chargeNorm (slow l b x)⁻¹ r V f ≤ YM.Push.Uniform.Decay b x y * feat b S R k := by
  let t := YM.Push.Uniform.Decay b x y
  let c := Real.exp (b*R)*k
  have ht : 0 < t := Real.exp_pos _
  have hc : 0 ≤ c := mul_nonneg (Real.exp_pos _).le he.bound
  have hi i (hi : i∈S) a (hx : a∈cube ι r) : |(slow l b x)⁻¹ i * pc i f a| ≤ t*c := by
    have hw : (separation x y:ℝ) ≤ (separation x (l i):ℝ)+(R:ℝ) := by
      have hh := (separation_triangle x (l i) y).trans (Nat.add_le_add_left
        (show separation (l i) y ≤ R from separation_comm y _ ▸ he.within i hi) _)
      exact_mod_cast hh
    have hp : (slow l b x)⁻¹ i ≤ t*Real.exp (b*R) := by
      unfold t
      rw [Pi.inv_apply, slow, ← Real.exp_neg, YM.Push.Uniform.Decay,← Real.exp_add]
      apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_left hw hb]
    unfold c; rw [abs_mul, abs_of_pos (show 0 < (slow l b x)⁻¹ i from inv_pos.mpr (slow_pos ..)), ← mul_assoc]
    exact mul_le_mul hp (he.interior _ hi _ hx) (abs_nonneg _) (mul_nonneg ht.le (Real.exp_pos _).le)
  exact (chargeNorm_fewer hr hV _ he.reg _ hi (mul_nonneg ht.le hc) he.exterior).trans_eq (by unfold feat c t; ring)

lemma featured (hr : 0 < r) (hV : Regular r 2 V) (he : 0 ≤ e) (hm : 0 < m) (hc : Charged r V 0)
    (hH : ∀ u∈cube ι r,YM.Push.Uniform.Charge (conjugated (slow l e x) (curvature V u)) m)
    (hF : Features l x R S r f k) (hG : Features l y R' T r g k') :
    |covariance r V f g| ≤ feat e S R k / m * (YM.Push.Uniform.Decay e x y * feat e T R' k') := by
  apply (normalized hr hV hc hm (fun i => (slow_pos l e x i).ne') hH hF.reg hG.reg).trans
  have h := div_le_div_of_nonneg_right (hF.pay hr hV he) hm.le
  exact mul_le_mul h (hG.gain hr hV x he) (chargeNorm_nn ..) ((div_nonneg (chargeNorm_nn ..) hm.le).trans h)


end YM.Primitives.SmallFieldExterior
