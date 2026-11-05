import YM.EveryPhase.Light
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Heat decay and continuity
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Filter Set Spec Boundary Next.BOUNDARY Spectral Mink Probe MeasureTheory Measure
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder

section decay
private lemma density_power (r : ℝ) (hr : 0 < r) :
    ∫ t : ℝ in Ioi 0, t^2 * Real.exp (-r*t) = r⁻¹ ^ 3 * Real.Gamma 3 := by
  convert Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=3) (by norm_num) hr using 1
  · norm_num [Real.rpow_two]
  rw [one_div,show (3:ℝ)= (↑(3:ℕ):ℝ) by norm_num,Real.rpow_natCast]

/-- Tail integration of the shell bound. Parameters outside the unit
interval can already be included at the same price using total mass. -/
theorem decay (μ : Measure E4) [IsFiniteMeasure μ] (C : ℝ) (_ : 0≤C)
    (h : ∀ u > (0:ℝ), μ.real (lowE u) ≤ C*u^2) (s : ℝ≥0) (hs : 0<s) :
    (∫ p in aboveE, boltz s p ∂μ) ≤ (C*Real.Gamma 3)*(s:ℝ)⁻¹^2 := by
  classical
  let r : ℝ := s
  have hr : 0 < r := hs
  let f (t : ℝ) := r * Real.exp (-r*t)
  let g (p : E4) := (Ici (time p)).indicator f
  let V := μ.restrict aboveE
  let T := volume.restrict (Ioi (0:ℝ))
  have hf : Integrable f T := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hr) 0).const_mul _
  have hg : Integrable (uncurry g) (V.prod T) := by
    let S := {x : E4 × ℝ | time x.1 ≤ x.2}
    have hv : MeasurableSet S := (isClosed_le (clock_cont.comp continuous_fst) continuous_snd).measurableSet
    have he : uncurry g=S.indicator (f ∘ Prod.snd) := by
      funext x; by_cases h : x ∈ S
      · exact (indicator_of_mem h (f:=f ∘ Prod.snd)).symm ▸ (indicator_of_mem h (s:=Ici (time x.1)) (f:=f))
      rw [indicator_of_notMem h]; exact indicator_of_notMem (s:=Ici (time x.1)) (a:=x.2) h f
    haveI : IsFiniteMeasure V := by unfold V; infer_instance
    rw [he]; exact (hf.comp_snd (μ:=V)).indicator hv
  haveI : SigmaFinite T := by unfold T; infer_instance
  haveI : SigmaFinite V := by unfold V; infer_instance
  calc
    _ = ∫ p, (∫ t, g p t ∂T) ∂V := by
      apply setIntegral_congr_fun aboveE_m; intro p (hp : p∈aboveE)
      have hk : Ici (time p) ⊆ Ioi 0 := fun t ht => show 0 < t from lt_of_lt_of_le (show 0<time p from hp) ht
      dsimp only [T,g]; rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict_of_subset hk, integral_Ici_eq_integral_Ioi]
      unfold f; rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hr)]
      change Real.exp (-r*time p) = _; field_simp
    _ = ∫ t, (∫ p, g p t ∂V) ∂T := integral_integral_swap hg
    _ ≤ ∫ t, (C*r)*(t^2 * Real.exp (-r*t)) ∂T := by
      have hb : Integrable (fun t => t^2 * Real.exp (-r*t)) T := by
        by_contra! hh
        have ht := integral_undef hh; dsimp only [T] at ht; rw [density_power r hr] at ht
        exact (ne_of_gt (by positivity)) ht
      apply integral_mono_ae hg.integral_prod_right (hb.const_mul _)
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
      have he : 0≤ f t := mul_nonneg hr.le (Real.exp_pos _).le
      let s' := {p | time p ≤ t}
      have hh : (g · t) = s'.indicator (fun _ => f t) := by
        ext p; by_cases h : p ∈ s'
        · rw [indicator_of_mem h]; exact indicator_of_mem (s:=Ici (time p)) (a:=t) h _
        rw [indicator_of_notMem h]; exact indicator_of_notMem (s:=Ici (time p)) (a:=t) h _
      have ht' : s' ∩ aboveE=lowE t := by ext p; exact and_comm
      change (∫ x : E4, g x t ∂V) ≤ _
      dsimp only [V]
      rw [hh,integral_indicator (measurableSet_le clock_cont.measurable measurable_const),
        Measure.restrict_restrict (measurableSet_le clock_cont.measurable measurable_const), ht', setIntegral_const,
        smul_eq_mul]
      apply (mul_le_mul_of_nonneg_right (h t ht) he).trans_eq
      unfold f; ring
    _ = _ := by
      rw [integral_const_mul]; dsimp only [T]; rw [density_power _ hr]; change _ = _ * r⁻¹^2
      field_simp
end decay

section continuity
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    {F : Final C f S} (L : Almanac F) (w : SumOfWords S)

theorem char_cont (p : E4) : Continuous fun i => charFun (νletter L i w) p := by
  let b := Poincare.translation p
  let u := acted F.action.spin b w
  apply (sum_pair L w u).congr
  intro i; rw [νletter,(L.cores i).spectral]
  have hv : u=acted (L.actors i).spin b w := by rw [L.spins i]
  rw [hv,cov_operator_vac (L.cores i)]; rfl

/-- For continuity of heat use the scalar spectral measure on spacetime frequencies.
Approximate the exponential on the positive cone uniformly by compact bumps
times the exponential. Fourier test against the translation functions. -/
lemma test_cont (g : Probe E4) : Continuous fun i => ∫ p, g p ∂νletter L i w := by
  let c i := charFun (νletter L i w)
  obtain ⟨M,hM,hm⟩ := word_bound L w
  have he i : (∫ p, c i p * hat g p)=pref E4 • ∫ p, g p ∂νletter L i w := wave_integral _ _
  let V i := ∫ p, g p ∂νletter L i w
  have hp : Continuous fun i => pref E4 • V i := by
    apply continuous_iff_continuousAt.mpr; intro i
    have hx (q : F.α.space.X) : pref E4 • V q= ∫ p, c q p*hat g p := (he q).symm
    dsimp only [ContinuousAt]; simp_rw [hx]
    apply tendsto_integral_filter_of_dominated_convergence (fun q => M * ‖hat g q‖)
    · refine Eventually.of_forall fun a => ?_
      exact (stronglyMeasurable_charFun (μ:=νletter L a w)).aestronglyMeasurable.mul
        (SchwartzMap.continuous _).aestronglyMeasurable
    · exact Eventually.of_forall fun i => ae_of_all _ fun p =>
        (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right ((norm_charFun_le p).trans (hm i)) (norm_nonneg _))
    · exact (hat g).integrable.norm.const_mul M
    exact ae_of_all _ fun p => ((char_cont L w p).tendsto i).mul tendsto_const_nhds
  apply (continuous_const (y:=(pref E4)⁻¹)).smul hp |>.congr
  intro i; change (pref E4)⁻¹ • (pref E4 • V i)=V i; rw [smul_smul, inv_mul_cancel₀ Probe.prepos.ne', one_smul]

theorem uniform_heat (s : ℝ≥0) (hs : 0<s) : Continuous fun i =>
    inner ℂ (stands (L.actors i).operators w) (bHeat (L.J i) s (stands (L.actors i).operators w)) := by
  have hr : 0<(s:ℝ) := hs
  simp_rw [fun i => bHeat_pair (L.links i) (L.cores i) s (stands (L.actors i).operators w)]
  let g i := ∫ p, boltz s p ∂νletter L i w
  suffices H : Continuous g from Complex.continuous_ofReal.comp H
  obtain ⟨M,hM,hm⟩ := word_bound L w
  -- use a bump in ALL E4 momenta, cone support makes Euclidean norm ≤ 2 p(timeAxis)
  have he (ε : ℝ) (hε : 0 < ε) : ∃ f : F.α.space.X → ℝ, Continuous f ∧ ∀ i, dist (g i) (f i) < ε := by
    have hp : Tendsto (fun x : ℝ => M * Real.exp (-(s:ℝ) * x)) atTop (𝓝 0) := by
      have hx := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hr))
      simpa using! hx.const_mul M
    obtain ⟨N,hN,hx⟩ := ((hp.eventually (gt_mem_nhds hε)).and (eventually_gt_atTop (0:ℝ))).exists
    have hn : 0 < N := hx
    let B : ContDiffBump (0:E4) := ⟨2*N,3*N,by positivity,by linarith⟩
    let F (p) := B p * boltz s p
    have hF : HasCompactSupport F := B.hasCompactSupport.mul_right
    let f : Probe E4 := (hF.comp_left (show Complex.ofReal 0=0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (B.contDiff.mul ((Real.contDiff_exp).comp (by fun_prop))))
    have hB : Continuous F := by unfold F; exact B.continuous.mul (by unfold boltz; fun_prop)
    have hw (i) : (∫ p, f p ∂νletter L i w).re=∫ p, F p ∂νletter L i w := by
      change (∫ p, (↑(F p):ℂ) ∂νletter L i w).re=_
      rw [integral_complex_ofReal, Complex.ofReal_re]
    refine ⟨fun i => ∫ p, F p ∂νletter L i w,
      (Complex.continuous_re.comp (test_cont L w f)).congr hw, fun i => ?_⟩
    let μ := νletter L i w
    have hh : ∀ᵐ p ∂μ, p ∈ cone := cave (L.cores i) _
    have hv : ∀ᵐ p ∂μ, 0 ≤ time p := hh.mono fun p hp => (cone_self p|>.mp hp).1
    let Q := Real.exp (-(s:ℝ)*N)
    have hu : ∀ᵐ p ∂μ, ‖boltz s p-F p‖ ≤ Q := by
      filter_upwards [hh] with p hp
      have hw : 0 ≤ boltz s p := Real.exp_pos _ |>.le
      by_cases H : p∈ Metric.closedBall (0:E4) (2*N)
      · change ‖_ - (B p * boltz s p)‖ ≤ _
        rw [B.one_of_mem_closedBall H,one_mul,sub_self,norm_zero]; exact (Real.exp_pos _).le
      have hA : N ≤ time p := by
        simp only [mem_closedBall_zero_iff, not_le] at H
        have hc : ‖spatial p‖ ≤ time p := hp
        have hg := Mink.squares p
        by_contra! hf
        nlinarith [norm_nonneg (spatial p)]
      unfold F; rw [Real.norm_eq_abs]
      apply le_trans (abs_of_nonneg (sub_nonneg.mpr (mul_le_of_le_one_left hw B.le_one))).le
      apply (sub_le_self _ (mul_nonneg B.nonneg hw)).trans
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hA (neg_nonpos.mpr hr.le))
    change dist (∫ p, boltz s p ∂μ) (∫ p, F p ∂μ)<ε
    rw [dist_eq_norm, ← integral_sub (boltz_int μ hv s) (hB.integrable_of_hasCompactSupport hF)]
    apply lt_of_le_of_lt (norm_integral_le_of_norm_le (integrable_const _) hu)
    rw [integral_const,smul_eq_mul]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hm i)
      (Real.exp_pos _).le) hN
  apply continuous_iff_continuousAt.mpr
  intro i
  apply Metric.tendsto_nhds.mpr; intro ε hε
  obtain ⟨f,hf,h⟩ := he (ε/4) (by positivity)
  filter_upwards [Metric.tendsto_nhds.mp (hf.tendsto i) (ε/4) (by positivity)] with x hx
  have hu := h x; have hv := h i; rw [dist_comm] at hv
  apply (dist_triangle _ (f x) _).trans_lt
  linarith [dist_triangle (f x) (f i) (g i)]

/-- Subtraction of the FULL zero-energy projection. -/
theorem inverse_square (h : finite w) : ∃ M : ℝ, 0≤M ∧ ∀ i, ∀ s ≥ (1:ℝ≥0),
    let A := stands (L.actors i).operators w
    let P := (L.actors i).momentum.region zeroE
    let r := inner ℂ A ((bHeat (L.J i) s - P) A)
    0 ≤ r ∧ r ≤ ↑(M*(s:ℝ)⁻¹^2) := by
  obtain ⟨B,hB,hW⟩ := word_bound L w
  obtain ⟨C,hC,hL⟩ := light_bound L w h
  let D := max B C
  have hD : 0≤ D := le_trans hC (le_max_right ..)
  have hI i (x : ℝ) (hx : 0 < x) : (νletter L i w).real (lowE x) ≤ D*x^2 := by
    by_cases H : x ≤ 1
    · exact (hL i x ⟨hx,H⟩).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _))
    refine le_trans (measureReal_mono (μ:=νletter L i w) (subset_univ _)) ((hW i).trans
      ((le_max_left B C).trans (le_mul_of_one_le_right hD (one_le_pow₀ (le_of_lt (lt_of_not_ge H))))))
  refine ⟨D*Real.Gamma 3, by positivity, fun i s hs => ?_⟩
  have hh := zero_lt_one.trans_le hs
  dsimp only
  rw [residual_pair (L.links i) (L.cores i) s]
  exact ⟨Complex.zero_le_real.mpr (integral_nonneg fun p => (Real.exp_pos _).le),
    Complex.real_le_real.mpr (decay _ _ hD (hI i) _ hh)⟩
end continuity
end YM.EveryPhase
