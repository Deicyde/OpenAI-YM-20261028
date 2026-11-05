import Mathlib.Probability.Distributions.Gaussian.Multivariate

set_option warningAsError false

/-!
# Uniform score budget on the common conditional Gaussian

Use full covariance, permit dependence and singular (can pass even to an unused 0 subsystem). Key issue dimension: ratio factors with endpoint coefficient weights with bounded sum, but read
in potentially a very large selection. Do not bound by an exponential moment costing C^volume.

* `conditional`: Laplace on any linear image of std gaussian, REAL energy conventions unit
variance, weighted moment with constants paying **sum of weights** rather than dimension.
Assumption adjoint ℓ² bound on that marginal/completion. No hypothesis of independence of
output coordinates. We use a second auxiliary standard Gaussian, pos exponential comparison
at linear arguments. Constants real; integral of a nonlinear exponential.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Gauss
open Filter Finset Function MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Classical

abbrev Row (I : Type) := I → ℝ

variable {I J : Type} [Fintype I] [Fintype J]

def squares (x : Row I) := ∑ i,x i ^2

def pay (w x : Row I) := ∑ i, w i*x i ^ 2

def crossed (u x : Row I) := ∑ i,u i * x i

def standard (I : Type) [Fintype I] : Measure (Row I) := Measure.pi (fun _ => gaussianReal 0 1)

instance (I : Type) [Fintype I] : IsProbabilityMeasure (standard I) := by unfold standard; infer_instance

private lemma viable {α : Type} [MeasurableSpace α] (f : α → ℝ) (μ : Measure α) (h : 0 < ∫ i,f i ∂μ) : Integrable f μ := by
  by_contra hh; exact h.ne' (integral_undef hh)

private lemma scalar (t : ℝ) : (∫ x, Real.exp (t*x) ∂gaussianReal 0 1)=Real.exp (t^2/2) := by
  simpa only [mgf,id_eq, NNReal.coe_one,one_mul,zero_mul,zero_add] using
    congrFun (mgf_id_gaussianReal (μ:=0) (v:=1)) t

lemma scattered (t : Row I) :
    Integrable (fun x => Real.exp (crossed t x)) (standard I) ∧
      ∫ x, Real.exp (crossed t x) ∂standard I=Real.exp (squares t/2) := by
  have h : ∫ x, Real.exp (crossed t x) ∂standard I=Real.exp (squares t/2) := by
    unfold crossed; simp_rw [Real.exp_sum]
    rw [standard,integral_fintype_prod_eq_prod (fun i x => Real.exp (t i*x))]; simp_rw [scalar]
    rw [←Real.exp_sum]; unfold squares; rw [Finset.sum_div]
  exact ⟨viable _ _ (h.symm ▸ (Real.exp_pos _)), h⟩

private lemma heat_one {t : ℝ} (h : 0 ≤ t) (he : t ≤ 1/4) :
    0 < (∫ x, Real.exp (t*x^2) ∂gaussianReal 0 1) ∧
      (∫ x, Real.exp (t*x^2) ∂gaussianReal 0 1) ≤ Real.exp (2*t) := by
  let b : ℝ := 1/2-t; have hb : 0 < b := by unfold b; linarith
  let p := 1-2*t; have hp : 0<p := by unfold p; linarith
  have hu : p=2*b := by unfold p b; ring
  have hx : ∫ x, Real.exp (t*x^2) ∂gaussianReal 0 1=(Real.sqrt p)⁻¹ := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
    have hg x : gaussianPDFReal 0 1 x • Real.exp (t*x^2) = (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-b*x^2) := by
      unfold gaussianPDFReal; rw [smul_eq_mul, mul_assoc, ← Real.exp_add]; simp only [NNReal.coe_one,mul_one,sub_zero]; unfold b; ring_nf
    simp_rw [hg]; rw [integral_const_mul,integral_gaussian]
    have he : Real.pi/b=2*Real.pi*p⁻¹ := by rw [hu]; field_simp
    rw [he,Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi),Real.sqrt_inv]; field_simp
  rw [hx]; constructor
  · positivity
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  have hg := Real.sq_sqrt hp.le; have hz : 0≤Real.sqrt p := by positivity
  have h' : 1 ≤ (1+2*t)*Real.sqrt p := by
    have hs : 1 ≤ (1+2*t)^2*p := by
      unfold p
      have ht : 0 ≤ 2-4*t-8*t^2 := by nlinarith
      nlinarith
    rw [← hg,← mul_pow] at hs; exact (le_of_sq_le_sq (show (1:ℝ)^2≤_ by simpa using hs) (by positivity))
  exact h'.trans (mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2*t)]) hz)

lemma thermal {t : Row I} (ht : ∀ i,0≤t i) (he : ∀ i,t i ≤ 1/4) :
    Integrable (fun x => Real.exp (pay t x)) (standard I) ∧ (∫ x, Real.exp (pay t x) ∂standard I) ≤ Real.exp (∑ i,2*t i) := by
  let f (i : I) (x : ℝ) := Real.exp (t i*x^2)
  let q i := ∫ x,f i x ∂(gaussianReal 0 1)
  have hz : ∫ x, Real.exp (pay t x) ∂standard I = ∏ i, q i := by
    unfold standard pay; simp_rw [Real.exp_sum]; exact integral_fintype_prod_eq_prod f
  have hf i := heat_one (ht i) (he i)
  refine ⟨viable _ _ (hz.symm ▸ (show 0 < ∏ i,q i from prod_pos fun i _ => (hf i).1)),?_⟩
  rw [hz,Real.exp_sum]; exact Finset.prod_le_prod (fun i _ => (hf i).1.le) fun i _ => (hf i).2

-- finite covariance generator with ℓ² *squared* bound (κ here do NOT confuse with beta)

def mapRows (q : I → J → ℝ) (x : Row J) : Row I := fun i => crossed (q i) x

def adjBound (q : I → J → ℝ) (K : ℝ) := ∀ y, squares (mapRows (Function.swap q) y) ≤ K*squares y

lemma rewrite_row (q : I → J → ℝ) (v : Row I) (y : Row J) : crossed v (mapRows q y) = crossed (mapRows (Function.swap q) v) y := by
  unfold crossed mapRows; simp_rw [crossed, Finset.mul_sum, Finset.sum_mul]; rw [sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; simp only [Function.swap]; ring

/-- Weighted nonlinear Laplace estimate. -/
theorem conditional (q : I → J → ℝ) (K : ℝ) (h : adjBound q K) (hK : 0 ≤ K) (w : Row I) (hw : ∀ i,0 ≤ w i)
    (he : ∀ i,K*w i ≤ 1/4) : Integrable (fun y => Real.exp (pay w (mapRows q y))) (standard J) ∧
      (∫ y, Real.exp (pay w (mapRows q y)) ∂standard J) ≤ Real.exp (∑ i,2*(K*w i)) := by
  let μ := standard I; let ν := standard J
  let u (x : Row I) (i) := Real.sqrt (2*w i)*x i
  let v (x : Row I) := mapRows (Function.swap q) (u x)
  let g := fun z : Row I × Row J => Real.exp (crossed (v z.1) z.2)
  have hm : Measurable g := by unfold g crossed v mapRows u; unfold crossed; fun_prop
  have hg (x : Row I) : (∫ y, g (x,y) ∂standard J)= Real.exp (squares (v x)/2) := (scattered (v x)).2
  have ht x : squares (u x)/2 = pay w x := by
    unfold squares u pay; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) (hw i))]; ring
  let t i := K*w i
  have hf x : Real.exp (squares (v x)/2) ≤ Real.exp (pay t x) := by
    apply le_trans (Real.exp_monotone (div_le_div_of_nonneg_right (h (u x)) (by norm_num)))
    apply le_of_eq; rw [mul_div_assoc,ht]; unfold pay t; rw [Finset.mul_sum]; simp_rw [mul_assoc]
  have he1 : Measurable fun x => Real.exp (squares (v x)/2) := by unfold v mapRows u crossed squares; fun_prop
  obtain ⟨hz,hZ⟩:=thermal (t:=t) (fun i => mul_nonneg hK (hw i)) he
  have hI : Integrable (fun x => Real.exp (squares (v x)/2)) (standard I) := hz.mono' he1.aestronglyMeasurable <|
    Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hf _
  have hn z : ‖g z‖ = g z := Real.norm_of_nonneg (Real.exp_pos _).le
  have hh : Integrable g ((standard I).prod (standard J)) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun x => (scattered (v x)).1,?_⟩
    simp_rw [hn,hg]; exact hI
  have hP y : ∫ x, g (x,y) ∂standard I=Real.exp (pay w (mapRows q y)) := by
    have hr (x : Row I) : crossed (v x) y = crossed (u (mapRows q y)) x := by
      unfold v; rw [←rewrite_row]; unfold crossed u; refine sum_congr rfl fun i _ => ?_; ring
    unfold g; dsimp only; simp_rw [hr]; rw [(scattered _).2,ht]
  simp_rw [←hP]; constructor
  · exact hh.integral_prod_right
  rw [integral_integral_swap (μ:=standard J) (ν:=standard I) (f:=fun y x => g (x,y)) hh.swap]; simp_rw [hg]; exact (integral_mono hI hz hf).trans hZ
end YM.Multi.Vacuum.Gauss
