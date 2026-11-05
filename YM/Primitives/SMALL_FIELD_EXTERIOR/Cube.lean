import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Pi





/-!
# Weighted integrals on the closed counting box

SUP coordinate bounds for the charts, but all charges and derivatives below
will use the L² **counting** metric. Continuous just on the box is enough for
L¹; seminorms here needn't see values outside. No division by volume yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter Metric MeasureTheory
open scoped BigOperators Topology ContDiff

abbrev Points (ι : Type) := ι → ℝ
variable {ι : Type} [Fintype ι]

def cube (ι : Type) [Fintype ι] (r : ℝ) : Set (Points ι) := closedBall 0 r

lemma cube_compact (r : ℝ) : IsCompact (cube ι r) := isCompact_closedBall _ _
lemma cube_meas (r : ℝ) : MeasurableSet (cube ι r) := (cube_compact _).measurableSet
lemma cube_pi {r : ℝ} (hr : 0 ≤ r) : cube ι r = Set.univ.pi (fun _ => Icc (-r) r) := by
  rw [cube, closedBall_pi _ hr]
  simp [Real.closedBall_eq_Icc]
lemma cube_iff {r : ℝ} (hr : 0 ≤ r) {x : Points ι} : x ∈ cube ι r ↔ ∀ i, |x i| ≤ r := by
  simp only [cube_pi hr, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left, abs_le]

def raw (r : ℝ) (V f : Points ι → ℝ) : ℝ := ∫ x in cube ι r, Real.exp (-V x) * f x

def bracket (r : ℝ) (V f g : Points ι → ℝ) := raw r V (f*g)

def size (r : ℝ) (V f : Points ι → ℝ) := Real.sqrt (bracket r V f f)

variable {r : ℝ} {V H f g h : Points ι → ℝ}

lemma raw_L1 (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r)) :
    IntegrableOn (fun x => Real.exp (-V x) * f x) (cube ι r) :=
  ((Real.continuous_exp.comp_continuousOn hV.neg).mul hf).integrableOn_compact (cube_compact _)
lemma raw_congr (he : EqOn f g (cube ι r)) : raw r V f = raw r V g :=
  setIntegral_congr_fun (cube_meas _) (fun i hi => by rw [he hi])
lemma raw_add (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r)) (hg : ContinuousOn g (cube ι r)) :
    raw r V (f+g)=raw r V f + raw r V g := by
  unfold raw
  simp only [Pi.add_apply, mul_add]; exact integral_add (raw_L1 hV hf) (raw_L1 hV hg)
lemma raw_sub (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r)) (hg : ContinuousOn g (cube ι r)) :
    raw r V (f-g)=raw r V f - raw r V g := by
  unfold raw
  simp only [Pi.sub_apply, mul_sub]; exact integral_sub (raw_L1 hV hf) (raw_L1 hV hg)
lemma raw_smul (k : ℝ) (r : ℝ) (V f : Points ι → ℝ) : raw r V (k • f) = k * raw r V f := by
  unfold raw; simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (Real.exp _ ) k, integral_const_mul]
lemma raw_sum {α : Type*} (hV : ContinuousOn V (cube ι r)) {f : α → Points ι → ℝ}
    (s : Finset α) (hi : ∀ i∈s, ContinuousOn (f i) (cube ι r)) :
    raw r V (∑ i∈s, f i)=∑ i∈s, raw r V (f i) := by
  unfold raw; simp only [Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum _ fun i h => raw_L1 hV (hi i h)
lemma raw_nonneg (he : ∀ x∈cube ι r, 0 ≤ f x) : 0 ≤ raw r V f :=
  setIntegral_nonneg (cube_meas _) fun x hx => mul_nonneg (Real.exp_pos _).le (he x hx)
lemma raw_mono (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r))
    (hg : ContinuousOn g (cube ι r)) (he : ∀ x∈cube ι r, f x ≤ g x) : raw r V f ≤ raw r V g :=
  setIntegral_mono_on (raw_L1 hV hf) (raw_L1 hV hg) (cube_meas _)
    (fun x hx => mul_le_mul_of_nonneg_left (he x hx) (Real.exp_pos _).le)
lemma raw_one_pos (hr : 0 < r) (hV : ContinuousOn V (cube ι r)) : 0 < raw r V 1 := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae _ (raw_L1 hV continuousOn_const)).mpr
  · have hx : support (fun x => Real.exp (-V x) * (1:ℝ)) ∩ cube ι r = cube ι r := by ext; simp
    change 0 < volume (support (fun x => Real.exp (-V x) * (1:ℝ)) ∩ cube ι r)
    rw [hx]
    exact (isOpen_ball.measure_pos volume ⟨0,mem_ball_self hr⟩).trans_le (measure_mono ball_subset_closedBall)
  exact Filter.Eventually.of_forall (fun x => mul_nonneg (Real.exp_pos _).le zero_le_one)
lemma raw_none (r : ℝ) (f : Points ι → ℝ) : raw r 0 f = ∫ x in cube ι r, f x := by simp [raw]

lemma self_nonneg (r : ℝ) (V f : Points ι → ℝ) : 0 ≤ bracket r V f f := raw_nonneg fun x _ => mul_self_nonneg (f x)
lemma bracket_sym (r : ℝ) (V f g : Points ι → ℝ) : bracket r V f g = bracket r V g f := by
  unfold bracket; rw [mul_comm]
lemma bracket_add (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r))
    (hg : ContinuousOn g (cube ι r)) (hh : ContinuousOn h (cube ι r)) :
    bracket r V (f+g) h = bracket r V f h + bracket r V g h := by unfold bracket; rw [add_mul]; exact raw_add hV (hf.mul hh) (hg.mul hh)
lemma bracket_sub (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r))
    (hg : ContinuousOn g (cube ι r)) (hh : ContinuousOn h (cube ι r)) :
    bracket r V (f-g) h = bracket r V f h - bracket r V g h := by unfold bracket; rw [sub_mul]; exact raw_sub hV (hf.mul hh) (hg.mul hh)
lemma bracket_smul (k : ℝ) (r : ℝ) (V f g : Points ι → ℝ) : bracket r V (k • f) g = k * bracket r V f g := by
  unfold bracket; rw [smul_mul_assoc, raw_smul]
lemma bracket_sum {α : Type*} (hV : ContinuousOn V (cube ι r)) {f : α → Points ι → ℝ} (s : Finset α)
    (hi : ∀ i∈s, ContinuousOn (f i) (cube ι r)) (hg : ContinuousOn g (cube ι r)) :
    bracket r V (∑ i∈s, f i) g=∑ i∈s, bracket r V (f i) g := by
  unfold bracket; rw [Finset.sum_mul]; exact raw_sum hV s fun i h => (hi i h).mul hg
lemma size_sq (r : ℝ) (V f : Points ι → ℝ) : size r V f ^ 2 = bracket r V f f := Real.sq_sqrt (self_nonneg r V f)
lemma size_nn (r : ℝ) (V f : Points ι → ℝ) : 0 ≤ size r V f := Real.sqrt_nonneg _
@[simp] lemma size_zero (r : ℝ) (V : Points ι → ℝ) : size r V 0 = 0 := by simp [size,bracket,raw]
lemma size_smul (k : ℝ) (r : ℝ) (V f : Points ι → ℝ) : size r V (k • f)= |k| * size r V f := by
  have h : size r V (k • f)^2=(|k| * size r V f)^2 := by
    rw [size_sq, bracket_smul, bracket_sym r V f (k • f), bracket_smul, mul_pow, sq_abs, size_sq]; ring
  exact (sq_eq_sq₀ (size_nn ..) (mul_nonneg (abs_nonneg _) (size_nn ..))).mp h
lemma size_mono (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r))
    (hg : ContinuousOn g (cube ι r)) (he : ∀ x∈cube ι r, |f x| ≤ |g x|) : size r V f ≤ size r V g :=
  Real.sqrt_le_sqrt (raw_mono hV (hf.mul hf) (hg.mul hg) fun x hx => by
    change f x * f x ≤ g x * g x; rw [← sq, ← sq]; exact sq_le_sq.mpr (he x hx))
lemma size_le_mul (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r)) (hg : ContinuousOn g (cube ι r))
    {k : ℝ} (hk : 0 ≤ k) (he : ∀ x∈cube ι r, |f x| ≤ k*|g x|) : size r V f ≤ k * size r V g := by
  have hh : ContinuousOn (k • g) _ := continuousOn_const.smul hg
  have hi : size r V f ≤ size r V (k • g) := size_mono hV hf hh fun x hx => by simpa [abs_mul,abs_of_nonneg hk] using he x hx
  simpa [size_smul,abs_of_nonneg hk] using hi
lemma cauchy (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r)) (hg : ContinuousOn g (cube ι r)) :
    |bracket r V f g| ≤ size r V f * size r V g := by
  have h (k : ℝ) : 0 ≤ bracket r V g g * (k*k) + (2*bracket r V f g)*k + bracket r V f f := by
    have he : ContinuousOn (k • g) (cube ι r) := continuousOn_const.smul hg
    have ht := self_nonneg r V (f+k • g)
    rw [bracket_add hV hf he (hf.add he), bracket_sym r V f (f+k • g), bracket_add hV hf he hf, bracket_smul,
      bracket_smul, bracket_sym r V g (f+k • g), bracket_add hV hf he hg, bracket_smul, bracket_sym r V g f] at ht
    linarith
  have hx := discrim_le_zero h
  unfold discrim at hx
  apply abs_le_of_sq_le_sq _ (mul_nonneg (size_nn ..) (size_nn ..))
  rw [mul_pow,size_sq,size_sq]; nlinarith only [hx]
lemma size_add (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r))
    (hg : ContinuousOn g (cube ι r)) : size r V (f+g) ≤ size r V f + size r V g := by
  have h := le_of_abs_le (cauchy hV hf hg)
  apply (sq_le_sq₀ (size_nn ..) (add_nonneg (size_nn ..) (size_nn ..))).mp
  rw [size_sq, bracket_add hV hf hg (hf.add hg), bracket_sym r V f (f+g), bracket_add hV hf hg hf,
    bracket_sym r V g (f+g), bracket_add hV hf hg hg, bracket_sym r V g f]
  nlinarith only [h,size_sq r V f,size_sq r V g]
lemma size_neg (r : ℝ) (V f : Points ι → ℝ) : size r V (-f)= size r V f := by simpa using size_smul (-1) r V f
lemma size_sub (hV : ContinuousOn V (cube ι r)) (hf : ContinuousOn f (cube ι r))
    (hg : ContinuousOn g (cube ι r)) : size r V (f-g) ≤ size r V f + size r V g := by
  simpa only [size_neg, sub_eq_add_neg] using size_add hV hf hg.neg
lemma size_sum {α : Type*} (hV : ContinuousOn V (cube ι r)) {f : α → Points ι → ℝ} (s : Finset α)
    (hi : ∀ i∈s, ContinuousOn (f i) (cube ι r)) : size r V (∑ i∈s, f i) ≤ ∑ i∈s, size r V (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hj ih =>
    have ht l (hl : l ∈ s) := hi l (Finset.mem_insert_of_mem hl)
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hc : ContinuousOn (∑ i∈s, f i) (cube ι r) := by
      have he : (∑ i∈s, f i)=fun x => ∑ i∈s, f i x := funext fun x => Finset.sum_apply ..
      rw [he]; exact continuousOn_finsetSum _ ht
    exact (size_add hV (hi i (Finset.mem_insert_self ..)) hc).trans
      (add_le_add (le_refl _) (ih ht))
end YM.Primitives.SmallFieldExterior
