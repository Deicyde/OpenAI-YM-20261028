import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Ac.Table
import YM.Analysis.Polydisc
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15
import YM.Work.B06


/-!
# Finite canonical stencil marginal, every dimension at its earned price

E.LXE/Jpr normalization. Provide Moment receipts with NOT an exponential
price in Gaussian dimension. Coordinate bounds permit geodesic/log fronts
to be unbounded in those coordinates pre-guard. Standard Gaussian used
during moving-covariance path comparison, not a decorrelation of the
actual fine Z.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Nimbuses
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
variable {E ι : Type*} [NormedAddCommGroup E]

abbrev Sky (ι : Type*) := EuclideanSpace ℝ ι

def breath (x:E) := 1+‖x‖
lemma breath_ge (x:E) : 1≤breath x := le_add_of_nonneg_right (norm_nonneg _)
lemma breath_nonneg (x:E) : 0≤breath x:=zero_le_one.trans (breath_ge _)
lemma continuous_breath (F : Type*) [NormedAddCommGroup F] : Continuous (breath (E:=F)):=continuous_const.add continuous_norm

variable [Fintype ι]

-- unconditional at any σ-fiber. pre-price.
lemma eval_drop (i : ι) : MeasurePreserving (fun x:Sky ι=> x i) (stdGaussian (Sky ι)) (gaussianReal 0 1) := by
  classical
  simpa using (measurePreserving_eval_multivariateGaussian (μ:=0) (Matrix.PosSemidef.one (n:=ι) (R:=ℝ)) (i:=i))

lemma grav (m : ℕ) : Integrable (fun x:ℝ=> breath x ^ m) (gaussianReal 0 1) := by
  classical
  let μ:=gaussianReal 0 1
  cases m with
  | zero => simp
  | succ n =>
    let m:=n+1
    let c:=fun x:ℝ=> 2^m *(1+‖x‖^m)
    have he := (IsGaussian.memLp_id μ (m:ℕ) (by simp)).integrable_norm_pow (show m≠0 from Nat.succ_ne_zero _)
    have ht : Integrable c μ := ((integrable_const (1:ℝ)).add he).const_mul _
    apply ht.mono' ((continuous_breath _).pow m|>.aestronglyMeasurable)
    refine Eventually.of_forall fun x=> ?_
    change ‖breath x ^ m‖ ≤ 2^m * (1+‖x‖^m)
    rw [Real.norm_of_nonneg (pow_nonneg (breath_nonneg _) _)]
    by_cases hh : ‖x‖≤1
    · have hx := pow_le_pow_left₀ (breath_nonneg x) (show breath x ≤ 2 by unfold breath; linarith) m
      exact hx.trans (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity)))
    have hg : 1≤‖x‖ := by linarith
    have hx := pow_le_pow_left₀ (breath_nonneg x) (show breath x ≤ 2*‖x‖ by unfold breath; linarith) m
    rw [mul_pow] at hx; exact hx.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))

def outsize (m : ℕ) := 1 + ∫ x:ℝ, breath x ^ m ∂gaussianReal 0 1
lemma outsize_ge (m : ℕ) : 1 ≤ outsize m := le_add_of_nonneg_right (integral_nonneg fun x=>pow_nonneg (breath_nonneg x) _)

lemma rains (ι : Type*) [Fintype ι] (m : ℕ) :
    let μ:=stdGaussian (Sky ι)
    let f:=fun x:Sky ι=> breath x ^ m
    Integrable f μ ∧ (∫ x,f x ∂μ) ≤ outsize m * (1+(Fintype.card ι:ℝ))^(m+1) := by
  classical
  intro μ f
  by_cases h : Nonempty ι; swap
  · haveI : IsEmpty ι:= ⟨fun i=>h ⟨i⟩⟩
    have hp (x : Sky ι) : ‖x‖=0 := by
      rw [show x=0 by ext y; exact isEmptyElim y]; exact norm_zero
    simp only [f,breath,hp,add_zero,one_pow]; constructor
    · change Integrable (fun _ : Sky ι=> (1:ℝ)) (stdGaussian (Sky ι)); exact integrable_const _
    unfold μ; simpa using outsize_ge m
  let y (i:ι) (x:Sky ι) := breath (x i)^m
  let C:=(Fintype.card ι:ℝ)
  have hc : 1≤C := by unfold C; exact_mod_cast (show 1 ≤ Fintype.card ι from Fintype.card_pos)
  let u:=1+C
  let f' (x:Sky ι) := u^m * ∑ i,y i x
  have hx i : Integrable (y i) μ := (eval_drop i).integrable_comp_of_integrable (grav _)
  have hw : Integrable f' μ := Integrable.const_mul (integrable_finsetSum Finset.univ (fun i _=> hx i)) _
  have he (x:Sky ι) : ‖f x‖ ≤ f' x := by
    rw [show ‖f x‖=f x from Real.norm_of_nonneg (pow_nonneg (breath_nonneg _) m)]
    obtain ⟨i,_,hi⟩:=Finset.exists_max_image Finset.univ (fun i=> ‖x i‖) (show (Finset.univ (α:=ι)).Nonempty from Finset.univ_nonempty)
    let g := breath (x i)
    have hh j : (x j)^2 ≤ g^2 := by
      rw [← sq_abs (x j)]; exact pow_le_pow_left₀ (norm_nonneg (x j)) ((hi _ (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)) 2
    have ha:=breath_ge (x i); change 1≤g at ha
    have hs : ‖x‖^2 ≤ C*g^2 := by rw [EuclideanSpace.real_norm_sq_eq]; simpa [C] using Finset.sum_le_sum (s:=Finset.univ) (fun i _=> hh i)
    have hl : breath x ≤ u*g := by
      have hL : ‖x‖≤C*g := by
        have hp : C*g^2 ≤ (C*g)^2 := by nlinarith [mul_nonneg (show 0≤C^2-C by nlinarith) (sq_nonneg g)]
        nlinarith [mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans ha)]
      unfold breath u; nlinarith
    have hf := pow_le_pow_left₀ (breath_nonneg x) hl m; rw [mul_pow] at hf
    refine hf.trans (mul_le_mul_of_nonneg_left ?_ (show 0≤u^m by unfold u; positivity))
    exact Finset.single_le_sum (f:=fun i=> y i x) (fun i _ => pow_nonneg (breath_nonneg _) _) (Finset.mem_univ i)
  have hF := hw.mono' (show AEStronglyMeasurable f μ from ((continuous_breath _).pow m).aestronglyMeasurable)
    (Eventually.of_forall he)
  refine ⟨hF,(integral_mono hF hw (fun x=>(le_abs_self (f x)).trans (he x))).trans ?_⟩
  unfold f'; rw [integral_const_mul, integral_finsetSum _ (fun i _=> hx i)]
  let a:= outsize m
  have hp:=outsize_ge m; have hu:=show 1≤u from le_add_of_nonneg_right (zero_le_one.trans hc)
  have hi i : (∫ x, y i x ∂μ) ≤ a := by
    let F (x:ℝ) := breath x^m
    calc
      _ = ∫ x, F x ∂(Measure.map (fun x:Sky ι=>x i) μ) := (integral_map (eval_drop i).measurable.aemeasurable ((continuous_breath _).pow m|>.aestronglyMeasurable)).symm
      _ ≤ _ := by rw [(eval_drop i).map_eq]; unfold a outsize; exact le_add_of_nonneg_left zero_le_one
  change _ ≤ a*u^(m+1); rw [pow_succ',mul_comm a,mul_assoc]
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=> hi i)) (show 0≤u^m by positivity))
  simp only [Finset.sum_const, nsmul_eq_mul,Finset.card_univ]; change u^m*(C*a)≤ _
  rw [mul_left_comm]; refine mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) ?_; unfold a; positivity
end YM.Planned.PrimaryIntegral295.Nimbuses
