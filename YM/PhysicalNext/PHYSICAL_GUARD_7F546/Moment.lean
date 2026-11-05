import YM.Next.ROTATIONS.GapTest
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Common
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Word
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Marginal



/-!
# Absolute moments on counting-space covariance marginals

Use the GCC word/probe estimate on the actual cloud, including its pooled
quadratic budget. Need upper bounds on entries of the covariance (and a
PSD covariance), not of a principal *precision* block. No factorization of
the Gaussian across physical links. The shift in this file is **forward**:
`shift C m` is the law of `m+z`, `z` distributed as `cloud C`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546
open MeasureTheory Function Filter Finset
open YM.Next.SectorChange.Gaussian YM.SectorTools.PhysicalGaussianSwitch
open scoped Topology BigOperators

variable {I : Type} [Fintype I]

/-- Use the Pi (sup) norm; `z` still has all the original counting/color coordinates. -/
def weight (q : ℕ) (z : Vec I) : ℝ := (1 + ‖z‖) ^ q

lemma weight_nonneg (q : ℕ) (z : Vec I) : 0 ≤ weight q z := by unfold weight; positivity
lemma weight_mono (z : Vec I) {q q' : ℕ} (h : q ≤ q') : weight q z ≤ weight q' z :=
  pow_le_pow_right₀ (by linarith only [norm_nonneg z]) h
lemma weight_add (q q' : ℕ) (z : Vec I) : weight (q + q') z = weight q z * weight q' z :=
  pow_add ..
lemma weight_continuous (q : ℕ) : Continuous (weight (I:=I) q) := by unfold weight; fun_prop

/-- Includes genuine integrability even in uses where the numerical
moment is zero. Always for the named measure, not some dominating product
measure substituted into the answer. -/
structure MomentBound (μ : Measure (Vec I)) (q : ℕ) (A : ℝ) : Prop where
  auth : Integrable (weight q) μ
  bound : (∫ z, weight q z ∂μ) ≤ A

/-- Reservation for the GCC word estimate. Chosen from a single cap `K`
on **read coordinates**, and a uniform bound `U` on covariance entries. -/
def reservation (K : ℕ) (U : ℝ) : ℝ := (8 * (1 + K * U))⁻¹
lemma reservation_pos (K : ℕ) {U : ℝ} (h : 0 ≤ U) : 0 < reservation K U := by
  unfold reservation
  positivity

/-- `M` bounds the magnitude of the shift in an individual coordinate. -/
def singlePrice (K q : ℕ) (U M : ℝ) : ℝ :=
  let r := reservation K U
  (YM.Primitives.GCC.Words.bulk r q M 1) ^ q * Real.exp (2 * (K * (r * U)))

lemma singlePrice_nonneg (K q : ℕ) (U : ℝ) {M : ℝ} (h : 0 ≤ M) :
    0 ≤ singlePrice K q U M :=
  mul_nonneg (pow_nonneg (YM.Primitives.GCC.Words.bulk_nn _ _ h _) _) (Real.exp_nonneg _)

/-- Price for `weight`. -/
def momentPrice (K q : ℕ) (U M : ℝ) : ℝ :=
  (2 : ℝ) ^ q * (1 + K * singlePrice K q U M)


-- No independence! Use the existing joint covariance and word estimates
-- even here (the polynomial has q occurrences of the SAME read coordinate i).
-- This exponential envelope is on the *unshifted* base of this Gaussian,
-- not a power of any likelihood; `pool_enough` pays for it.
open YM.Multi.Vacuum.Gauss YM.Primitives.GCC in
theorem coordinate_moment [DecidableEq I] (C : YM.Next.SectorChange.Gaussian.Table I)
    (hC : C.PosSemidef) {K : ℕ} (hK : Fintype.card I ≤ K)
    {U : ℝ} (hU : 0 ≤ U) (hEntry : ∀ i j, |C i j| ≤ U)
    (m : Vec I) (i : I) {M : ℝ} (hm : |m i| ≤ M) (q : ℕ) :
    Integrable (fun z : Vec I => |z i| ^ q) (shift C m) ∧
      (∫ z, |z i| ^ q ∂shift C m) ≤ singlePrice K q U M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hm
  let s : Finset Unit := {()}
  let r := reservation K U
  have hr : 0 < r := reservation_pos K hU
  have hk : (Fintype.card I : ℝ) ≤ K := Nat.cast_le.mpr hK
  let w : Unit → Vec I := fun _ _ => r
  let A := Common.cable (V:=Unit) C
  have hPool : Common.pool s C w := by
    refine Common.scaled C (K * U) (by positivity) (fun a => ?_)
      (fun j hj t => hr.le) (fun t => ?_)
    · calc
        _ ≤ ∑ _b : I, U := sum_le_sum fun b _ => hEntry a b
        _ = Fintype.card I * U := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hk hU
    · simp [s, w, r, reservation]
  have hd : Moment.due s A w ≤ K * (r * U) := by
    unfold A
    rw [Common.common_due C hC]
    simp only [s, sum_singleton, w]
    calc
      _ ≤ ∑ _b : I, r * U := by
        apply sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hEntry _ _)) hr.le
      _ = Fintype.card I * (r * U) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hk (by positivity)
  let B := Words.bulk r q M 1
  let m' : I → ℂ := fun j => m j
  let leg : Fin q → I := fun _ => i
  let word := Words.verse m' 1 univ leg
  let v : Probes Unit I := fun _ => word
  let H : Unit → ℕ → ℝ := fun _ => Words.weight 1 B q
  have hWord : Probe.Valid s 0 v w H := by
    refine ⟨fun u hu => ?_⟩
    have he := Words.price m' 1 q (w u) (fun _ => hr.le) hr hM leg 0 univ (by simp)
      (fun j _ => ⟨le_rfl, by simpa [m', leg, Real.norm_eq_abs] using hm⟩)
    simpa only [H, v, word, B, card_univ, Fintype.card_fin] using he
  obtain ⟨hi, he⟩ := Moment.revenues (Common.pool_enough C hC hPool) hWord (Finset.Subset.refl s)
  -- Transport back to the actual correlated cloud. Use the theorem giving
  -- the map, not a new product-law hypothesis.
  have hw : Continuous word := hWord.read () (mem_singleton_self _)
  have hmap : MeasurePreserving (mapRows (A ())) (standard I) (cloud C) := Common.paid_one C
  have hpay := pay_pull hmap (fun z => ‖word z‖)
    hw.norm.aestronglyMeasurable
  have hval (x : Vec I) : Moment.values s A v x = word (mapRows (A ()) x) := by
    simp only [Moment.values, s, prod_singleton, v]
  have hauth : Integrable (fun z => ‖word z‖) (cloud C) := by
    apply hpay.1.mp
    have hh : Integrable (fun x => ‖Moment.values s A v x‖) (standard I) := hi.norm
    simp_rw [← hval]
    exact hh
  have hbound : (∫ z, ‖word z‖ ∂cloud C) ≤ B ^ q * Real.exp (2 * (K * (r * U))) := by
    rw [← hpay.2]
    simp_rw [← hval]
    apply he.trans
    simp only [s, prod_singleton, H, Words.weight]
    simp only [Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero, pow_zero, mul_one, one_mul]
    apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_)
      (pow_nonneg (Words.bulk_nn _ _ hM _) _)
    exact mul_le_mul_of_nonneg_left hd (by norm_num)
  have hwNorm (z : Vec I) : ‖word z‖ = |(m + z) i| ^ q := by
    change ‖Words.verse m' 1 _ leg z‖ = _
    simp only [Words.verse, leg, Words.entry, m', one_mul, prod_const, card_univ,
      Fintype.card_fin, norm_pow, ← Complex.ofReal_add]
    rw [Complex.norm_real, Real.norm_eq_abs, Pi.add_apply]
  obtain ⟨h1,h2⟩ := shift_int C m (fun z => |z i| ^ q)
  rw [h1,h2]
  simp_rw [← hwNorm]
  exact ⟨hauth, hbound⟩

private lemma weight_bound (q : ℕ) (z : Vec I) :
    weight q z ≤ (2 : ℝ)^q * (1 + ∑ i, |z i| ^ q) := by
  have hsum : 0 ≤ ∑ i, |z i| ^ q := sum_nonneg fun i _ => by positivity
  by_cases h : ‖z‖ ≤ 1
  · apply le_trans (b:=(2:ℝ)^q)
      (pow_le_pow_left₀ (by change 0 ≤ 1 + ‖z‖; positivity) (by linarith) _)
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  cases isEmpty_or_nonempty I with
  | inl he =>
    exact False.elim (h ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
      (fun i => isEmptyElim i)))
  | inr he =>
    classical
    obtain ⟨i, hi, he⟩ := exists_max_image univ (fun i => |z i|) univ_nonempty
    have hk : ‖z‖ ≤ |z i| :=
      (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
        (fun j => (Real.norm_eq_abs _).trans_le (he j (mem_univ _)))
    calc
      weight q z ≤ (2 * |z i|) ^ q :=
        pow_le_pow_left₀ (by change 0 ≤ 1 + ‖z‖; positivity) (by linarith) _
      _ ≤ _ := by
        have hu : |z i| ^ q ≤ ∑ j, |z j| ^ q :=
          single_le_sum (f:=fun j => |z j| ^ q) (fun _ _ => by positivity) hi
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

attribute [local instance] shift_probability

/-- Uniform over covariance marginals with the same upper / mean prices.
No binding to a particular degree before this estimate. -/
theorem shifted_moments [DecidableEq I] (C : YM.Next.SectorChange.Gaussian.Table I) (hC : C.PosSemidef)
    {K : ℕ} (hK : Fintype.card I ≤ K) {U : ℝ} (hU : 0 ≤ U) (hEntry : ∀ i j, |C i j| ≤ U)
    (m : Vec I) {M : ℝ} (hM : 0 ≤ M) (hm : ∀ i, |m i| ≤ M) (q : ℕ) :
    MomentBound (shift C m) q (momentPrice K q U M) := by
  let μ := shift C m
  let f i (z : Vec I) := |z i| ^ q
  have h i := coordinate_moment C hC hK hU hEntry m i (hm i) q
  have hS : Integrable (fun z => ∑ i, f i z) μ := integrable_finsetSum _ fun i _ => (h i).1
  let g (z : Vec I) : ℝ := 2 ^ q * (1 + ∑ i, f i z)
  have hi : Integrable g μ := ((integrable_const 1).add hS).const_mul ((2 : ℝ) ^ q)
  have hw : Integrable (weight q) μ :=
    hi.mono' (weight_continuous _).aestronglyMeasurable (Eventually.of_forall
      (fun z => (Real.norm_of_nonneg (weight_nonneg q z)).trans_le (weight_bound q z)))
  refine ⟨hw, (integral_mono hw hi (weight_bound q)).trans ?_⟩
  change (∫ z, g z ∂μ) ≤ _
  unfold g momentPrice
  haveI : IsProbabilityMeasure μ := shift_probability ..
  rw [integral_const_mul, integral_add (integrable_const _) hS]
  simp only [integral_const, probReal_univ, one_smul]
  apply mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) (by positivity)
  rw [integral_finsetSum]
  · calc
      _ ≤ ∑ _i : I, singlePrice K q U M := sum_le_sum fun i _ => (h i).2
      _ = Fintype.card I * singlePrice K q U M := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK) (singlePrice_nonneg K q U hM)
  · exact fun i _ => (h i).1







end YM.PhysicalNext.PhysicalGuard7f546
