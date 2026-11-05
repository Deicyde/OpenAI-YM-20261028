import YM.Bid.Tar
import YM.Spark.Limit
/-!
# Identification of a strictly damped contour as a function

For fixed interior imaginary coordinates, `Aurora.shape` already gives us the
attenuation as a Schwartz test: take real coordinates zero. To obtain control
at all real coordinates, turn the phase multiplying this test into a
translation on its Fourier transform. Estimates here are for the actual
Schwartz topology. Use `Spark.allowance` first with compactly supported
position test, then the Schwartz cutoff limit -- no Bochner integral in a
putative Banach space of Schwartz tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C14
open Function Set Filter MeasureTheory Boundary Boundary.Probe
open scoped Topology BigOperators ContDiff InnerProductSpace

section translations

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- A bound polynomial in the norm of the translation. -/
def shiftCost (g : Probe X) (i j : ℕ) (x : X) : ℝ :=
  2 ^ i * (size i j g + ‖x‖ ^ i * size 0 j g)

lemma shiftCost_nonneg (g : Probe X) (i j : ℕ) (x : X) : 0 ≤ shiftCost g i j x := by
  unfold shiftCost size
  positivity

lemma shiftCost_cont (g : Probe X) (i j : ℕ) : Continuous (shiftCost g i j) := by
  unfold shiftCost
  fun_prop

lemma deriv_ahead (g : Probe X) (j : ℕ) (x u : X) :
    iteratedFDeriv ℝ j (ahead x g) u = iteratedFDeriv ℝ j g (u-x) := by
  change iteratedFDeriv ℝ j (fun z => g (z-x)) u = _
  exact iteratedFDeriv_comp_sub j x u

lemma ahead_bound (g : Probe X) (i j : ℕ) (x : X) : size i j (ahead x g) ≤ shiftCost g i j x := by
  refine (ahead x g).seminorm_le_bound ℂ i j (shiftCost_nonneg ..) fun u => ?_
  rw [deriv_ahead]
  have h : ‖u‖ ≤ ‖u-x‖ + ‖x‖ := by simpa using norm_add_le (u-x) x
  let A := ‖iteratedFDeriv ℝ j g (u-x)‖
  have hA : 0 ≤ A := norm_nonneg _
  change ‖u‖ ^ i * A ≤ _
  rcases le_total ‖x‖ ‖u-x‖ with H|H
  · calc
      ‖u‖ ^ i * A ≤ (2*‖u-x‖) ^ i * A :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i) hA
      _ = 2 ^ i * (‖u-x‖ ^ i * A) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ i * size i j g :=
        mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℂ i j g (u-x)) (by positivity)
      _ ≤ shiftCost g i j x := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (by unfold size; positivity)) (by positivity)
  calc
    ‖u‖ ^ i * A ≤ (2*‖x‖) ^ i * A :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i) hA
    _ ≤ (2*‖x‖) ^ i * size 0 j g := mul_le_mul_of_nonneg_left
      (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g j (u-x)) (by positivity)
    _ = 2 ^ i * (‖x‖ ^ i * size 0 j g) := by rw [mul_pow, mul_assoc]
    _ ≤ shiftCost g i j x := mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (by unfold size; positivity)) (by positivity)

/-- Any one continuous distribution costs only a finite sum of the polynomials. -/
lemma dist_ahead_bound (w : Distn X) (g : Probe X) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ x : X, ‖w (ahead x g)‖ ≤ C * ∑ p ∈ s, shiftCost g p.1 p.2 x := by
  let q := (normSeminorm ℂ ℂ).comp w.toLinearMap
  have hq : Continuous q := continuous_norm.comp w.continuous
  obtain ⟨s,C,_,hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X ℂ) q hq
  refine ⟨s,C,C.coe_nonneg,fun x => ?_⟩
  have h : ‖w (ahead x g)‖ ≤ (C:ℝ) * s.sup (schwartzSeminormFamily ℂ X ℂ) (ahead x g) :=
    hC (ahead x g)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ C.coe_nonneg)
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun p _ => shiftCost_nonneg ..) fun p hp => ?_
  exact (ahead_bound g p.1 p.2 x).trans (Finset.single_le_sum
    (f := fun u => shiftCost g u.1 u.2 x) (fun i _ => shiftCost_nonneg ..) hp)

variable [FiniteDimensional ℝ X]

lemma ahead_cont (g : Probe X) : Continuous fun x => ahead x g := by
  refine continuous_iff_continuousAt.mpr fun x => Spark.ready ?_ ?_
  · intro n b
    simp_rw [Spark.Jet, deriv_ahead]
    have hg := (g.smooth n).continuous_iteratedFDeriv (m := n) le_rfl
    exact (hg.tendsto (b-x)).comp (tendsto_snd.sub tendsto_fst)
  intro i j
  let C := shiftCost g i j x + 1
  refine ⟨C, ?_⟩
  have hlt : shiftCost g i j x < C := lt_add_one _
  exact (((shiftCost_cont g i j).tendsto x).eventually (gt_mem_nhds hlt)).mono
    fun v hv => (ahead_bound g i j v).trans (show shiftCost g i j v < C from hv).le

variable [MeasurableSpace X] [BorelSpace X]

lemma shiftCost_integrable (g f : Probe X) (i j : ℕ) :
    Integrable (fun x : X => shiftCost g i j x * ‖f x‖) := by
  have h0 := f.integrable (μ := volume)
  have hk := f.integrable_pow_mul volume i
  have heq : (fun x : X => shiftCost g i j x * ‖f x‖) =
      (fun x : X => 2 ^ i * (size i j g * ‖f x‖ + size 0 j g * (‖x‖ ^ i * ‖f x‖))) := by
    funext
    unfold shiftCost
    ring
  rw [heq]
  exact (((h0.norm.const_mul _).add (hk.const_mul _)).const_mul _)

lemma ahead_integrable (c : ℂ) (w : Distn X) (g f : Probe X) :
    Integrable (fun x : X => c * w (ahead x g) * f x) := by
  have hh : Continuous (fun x : X => c * w (ahead x g) * f x) :=
    (continuous_const.mul (w.continuous.comp (ahead_cont g))).mul f.continuous
  obtain ⟨s,C,_,h⟩ := dist_ahead_bound w g
  let P (x : X) := ‖c‖ * C * ∑ p ∈ s, shiftCost g p.1 p.2 x * ‖f x‖
  have hi : Integrable P :=
    (integrable_finsetSum s (fun p _ => shiftCost_integrable g f p.1 p.2)).const_mul _
  refine hi.mono' hh.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  calc
    ‖c * w (ahead x g) * f x‖ = ‖c‖ * ‖w (ahead x g)‖ * ‖f x‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖c‖ * (C * ∑ p ∈ s, shiftCost g p.1 p.2 x) * ‖f x‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)) (norm_nonneg _)
    _ = P x := by simp only [P, ← Finset.sum_mul, mul_assoc]

end translations
section modulation

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
variable (g : Probe X) (L : X → Probe X) (hL : ∀ x b : X, L x b = plane b x * g b)
include hL

lemma modulation_eq : L = (fun x => port (ahead x (hat g))) := by
  have hh (x : X) : hat (L x) = ahead x (hat g) := by
    ext1 p
    rw [ahead_at, hat_eq, hat_eq]
    refine integral_congr_ae (ae_of_all _ fun b => ?_)
    dsimp only
    rw [hL, ← mul_assoc, ← plane_add, show -p+x=-(p-x) by abel]
  funext x
  rw [← hh x, comes]

lemma modulation_cont : Continuous L := by
  rw [modulation_eq g L hL]
  exact port.continuous.comp (ahead_cont _)

lemma modulation_integrable (w : Distn X) (f : Probe X) :
    Integrable (fun x => ((pref X)⁻¹ : ℂ) * w (L x) * f x) := by
  rw [modulation_eq g L hL]
  exact ahead_integrable _ (w.comp port) _ _

/-- Pass the distribution through a compact integral with the indicated
absolute (radian) Fourier normalization. -/
lemma modulation_compact (w : Distn X) (f : Probe X) (hf : HasCompactSupport ⇑f) :
    w (sew g (port f)) = ∫ x, ((pref X)⁻¹ : ℂ) * w (L x) * f x := by
  let K := tsupport f
  have hk : IsCompact K := hf
  have hm : MeasurableSet K := hk.measurableSet
  let μ : Measure K := (volume : Measure X).comap ((↑) : K → X)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hk
  haveI : IsFiniteMeasure μ := by
    constructor
    unfold μ
    rw [(MeasurableEmbedding.subtype_coe hm).comap_apply, image_univ, Subtype.range_coe]
    exact hk.measure_lt_top
  -- both the probe family F (parameter x) and scalar integrands in x vanish off K
  have hsub (a : X → ℂ) (h : ∀ x, x ∉ K → a x = 0) : (∫ x : K, a x ∂μ) = ∫ x, a x :=
    (integral_subtype_comap hm a).trans (setIntegral_eq_integral_of_forall_compl_eq_zero h)
  let c := ((pref X)⁻¹ : ℂ)
  let F : X → Probe X := fun x => (c * f x) • L x
  have hzero (x : X) (h : x ∉ K) : F x = 0 := by
    have hx : f x = 0 := image_eq_zero_of_notMem_tsupport h
    simp [F, hx]
  have he (b : X) : sew g (port f) b = ∫ x : K, F x b ∂μ := by
    rw [hsub (fun x => F x b) (by intro x hx; simp [hzero x hx]), sews, port_eq]
    rw [Complex.real_smul]
    -- `c` uses the inverse with complex coercion; agree with `port_eq`.
    have hc : (((pref X)⁻¹ : ℝ) : ℂ) = c := by simp [c]
    rw [hc, ← mul_assoc, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change g b * c * (plane x b * f x) = ((c * f x) • L x) b
    simp only [_root_.smul_apply, smul_eq_mul, hL, plane_dot x b]
    ring
  have hc : Continuous F := (continuous_const.mul f.continuous).smul (modulation_cont g L hL)
  rw [Spark.allowance μ (fun x : K => F x) (sew g (port f)) he (hc.comp continuous_subtype_val) w,
    hsub (fun x => w (F x)) (by intro x hx; rw [hzero x hx, map_zero])]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change w ((c * f x) • L x) = c * w (L x) * f x
  rw [map_smul, smul_eq_mul, mul_right_comm]

lemma modulation_all (w : Distn X) (f : Probe X) :
    w (sew g (port f)) = ∫ x, ((pref X)⁻¹ : ℂ) * w (L x) * f x := by
  let c := ((pref X)⁻¹ : ℂ)
  let a (q : Probe X) (x : X) := c * w (L x) * q x
  have hi (q) : Integrable (a q) := modulation_integrable g L hL w q
  have hd (k : ℕ) (x : X) : ‖a (cap k f) x‖ ≤ ‖a f x‖ := by
    have hb : ‖keeper k x‖ ≤ 1 := by
      rw [keeper, along_at, tinted, Complex.norm_real, Real.norm_of_nonneg stall.nonneg]
      exact stall.le_one
    have heq : a (cap k f) x = a f x * keeper k x := by
      unfold a cap
      rw [sews]
      ring
    rw [heq, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hb
  have ha (x : X) : Tendsto (fun k => a (cap k f) x) atTop (𝓝 (a f x)) := by
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have he : (N:ℝ) ≤ n := by exact_mod_cast hn
    have ht : keeper n x = 1 := keeper_one n (le_trans (le_trans hN.le he) (by linarith))
    change a f x = a (cap n f) x
    simp only [a, cap, sews, ht, one_mul]
  have hr := tendsto_integral_of_dominated_convergence (fun x => ‖a f x‖)
    (fun k => (hi (cap k f)).aestronglyMeasurable) (hi f).norm
    (fun k => ae_of_all _ (hd k)) (ae_of_all _ ha)
  let J := w.comp ((sew g).comp port)
  have hl := (J.continuous.tendsto f).comp (persistent f)
  exact tendsto_nhds_unique_of_eventuallyEq hl hr (Eventually.of_forall fun k =>
    modulation_compact g L hL w (cap k f) (finite_cap k))

end modulation

open Mink Bid Boundary.Surface

section income

variable {G : Gauge} {L : Register G} {S : Table L}
variable {W : Surface S} {D : ∀ i, Blanket i}

/-- For fixed strictly admissible imaginary part. No change of regulator or
uniform bound as the imaginary part varies is needed here. -/
lemma emit_integral (Y : W.Aurora D) (n : ℕ) (v : Fin n → S.Union)
    (y : Points n) (h : y ∈ fields n) (hm : (D n).Modified) (f : Joint n) :
    (D n).partialD (W.W n v) y f = (∫ x, Y.emit v (glow x y) * f x) ∧
    Integrable (fun x => Y.emit v (glow x y) * f x) := by
  let P (x : Points n) := Y.lens n (glow x y)
  let g := P 0
  let w := Distn.fourier (W.W n v)
  have hP (x b : Points n) : P x b = plane b x * (D n).attenuate y b := by
    have hy : glow x y ∈ tube n := by simpa only [tube, mem_preimage, im_glow] using h
    simp only [P, Y.shape n _ hy, Blanket.lens, re_glow, im_glow]
  have hg (b : Points n) : g b = (D n).attenuate y b := by simp only [g, hP, plane_zero, one_mul]
  have hL (x b : Points n) : P x b = plane b x * g b := by rw [hP, hg]
  have he (q : Probe (Points n)) : (D n).diffuser y q = sew g q := by
    ext1 x
    rw [Blanket.diffuser, SchwartzMap.smulLeftCLM_apply_apply (hm.actual y (warmer n h)),
      sews, hg]
    rfl
  refine ⟨?_, modulation_integrable g P hL w f⟩
  change w ((D n).diffuser y (port f)) = _
  rw [he]
  exact modulation_all g P hL w f

end income

theorem answer : YM.Bid.C14 := by
  intro G L S W D hm _ _ Y _
  exact ⟨fun n v y h f => (emit_integral Y n v y h (hm n) f).1,
         fun n v y h f => (emit_integral Y n v y h (hm n) f).2⟩

end YM.Work.C14
