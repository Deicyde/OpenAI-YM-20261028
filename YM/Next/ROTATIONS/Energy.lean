import YM.Next.ROTATIONS.Response
/-! # Tested spectral response estimates at fixed scales: shape constants versus growing scales. -/
noncomputable section
namespace YM.Outer
open Function Filter Set Metric MeasureTheory Measure Complex Boundary Probe Nodes
open scoped Topology ContDiff BigOperators InnerProductSpace NNReal ENNReal

lemma lamp_top (m s f E) (hs : 0<s) (hf : Ends f) (h : Plus f) (hE : 0<E) (A : ℝ)
    (ha : ∀ p,f p ≠ 0 → ∀ v,sun v≠0 → kernel m (s*v) p E ≤ A) :
    Mlamp m s f E ≤ 2*E*directLap E f*A := by
  rw [lamp_lit _ _ _ E hE, sunny m s hs f hf E hE,mul_assoc (2*E)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hl : directLap E f*A = ∫ v, sun v*(directLap E f*A) := by rw [integral_mul_const, show (∫ v,sun v)=1 by simpa [counts] using sun_mass,one_mul]
  conv_rhs => rw [hl]
  apply integral_mono (sunny_m f hf hE) (sun.integrable.mul_const _)
  intro v
  by_cases H : sun v=0
  · simp [H]
  refine mul_le_mul_of_nonneg_left ?_ (sun_plus _)
  unfold directLap positiveLap
  rw [← integral_mul_const]; refine integral_mono (hf.paid ((raw_c hE).mul (slice_cont _ _ _ _ hE))) ((hf.paid (raw_c hE)).mul_const _) fun p => ?_
  by_cases h0 : f p=0; · simp [h0]
  rw [← mul_assoc]; gcongr
  · exact mul_nonneg (h _) (raw_n _ _)
  exact ha p h0 v H
lemma lamp_bottom (m s f E) (hs : 0<s) (hf : Ends f) (hg : Plus f) (hE : 0<E) (A : ℝ)
    (ha : ∀ p,f p ≠ 0 → ∀ v,sun v≠0 → A ≤ kernel m (s*v) p E) :
    2*E*directLap E f*A ≤ Mlamp m s f E := by
  rw [lamp_lit _ _ _ E hE,sunny m s hs f hf E hE,mul_assoc (2*E)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hl : directLap E f*A = ∫ v, sun v*(directLap E f*A) := by rw [integral_mul_const, show (∫ v,sun v)=1 by simpa [counts] using sun_mass,one_mul]
  conv_lhs => rw [hl]
  refine integral_mono (sun.integrable.mul_const _) (sunny_m f hf hE) fun v => ?_
  by_cases H : sun v=0; · simp [H]
  refine mul_le_mul_of_nonneg_left ?_ (sun_plus _)
  unfold directLap positiveLap
  rw [← integral_mul_const]; refine integral_mono ((hf.paid (raw_c hE)).mul_const _) (hf.paid ((raw_c hE).mul (slice_cont _ _ _ _ hE))) fun p => ?_
  by_cases h : f p=0; · simp [h]
  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left (ha p h v H) (mul_nonneg (hg _) (raw_n _ _))

lemma raw_mass (E : ℝ) (hE : 0<E) : ∫ p : ℝ,raw E p=Real.pi/E := by
  have he := Measure.integral_comp_mul_left (raw E) E
  rw [abs_of_pos (inv_pos.mpr hE), smul_eq_mul] at he
  have h p : raw E (E*p)=E⁻¹^2*(1+p^2)⁻¹ := by
    unfold raw; rw [show (E*p)^2+E^2=E^2*(1+p^2) by ring,mul_inv,inv_pow]
  simp_rw [h] at he
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at he
  field_simp at he ⊢
  linarith

lemma Mlamp_cont (m s f) : ContinuousOn (Mlamp m s f) (Ici 0) := Complex.continuous_re.comp_continuousOn (Lap_cont 1 (by norm_num) _)
lemma to_zero (f : ℝ → ℝ) (hf : ContinuousWithinAt f (Ici 0) 0) : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
  hf.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- Low-frequency payoff `w⁻¹`; proof also at 0. -/
lemma upper (m s f E) (hs : 0<s) (hf : Ends f) (hg : Plus f) (hE : 0≤E) (hR : Room f s) (T : ℝ) (ht : ∀ p,f p≤T) :
    Mlamp m s f E ≤ T*(2*Real.pi) := by
  have hh (E) (hE : 0<E) : Mlamp m s f E ≤ T*(2*Real.pi) := by
    have hz := lamp_top m s f E hs hf hg hE 1 (fun p hp v hv => (kernel_box _ _ _ _ _ hs hv (hR p hp)).2)
    rw [mul_one] at hz
    have h : directLap E f ≤ ∫ p,T*raw E p := integral_mono (hf.paid (raw_c hE))
      ((Integrable.of_integral_ne_zero (by rw [raw_mass E hE]; positivity)).const_mul T) (fun p => mul_le_mul_of_nonneg_right (ht _) (raw_n ..))
    rw [integral_const_mul,raw_mass E hE] at h
    exact (hz.trans (mul_le_mul_of_nonneg_left h (by positivity))).trans_eq (by field_simp)
  rcases eq_or_lt_of_le hE with rfl|he; swap; · exact hh E he
  apply le_of_tendsto (to_zero _ (Mlamp_cont m s f _ self_mem_Ici))
  filter_upwards [self_mem_nhdsWithin] with t ht; exact hh t ht

/-- Exponent D independent of m, enabled by choosing m later. -/
lemma off (m s f) (hs : 1≤s) (hf : Ends f) (hg : Plus f) (hr : Room f s) (E : ℝ) (he : 1≤E) (D : ℕ) (hD : D ≤ 2*m) :
    Mlamp m s f E ≤ (1 + kernelPrice m) * (2*tally 0 f) * (s/E)^D := by
  have hS : 0<s := by linarith
  have hE : 0<E := by linarith
  have hk := kernel_price_pos m
  have hu p (hp : f p ≠ 0) (v) (hv : sun v≠0) : kernel m (s*v) p E ≤ (1 + kernelPrice m)*(s/E)^D := by
    by_cases h : 1 ≤ s/E
    · apply (kernel_box m _ _ _ _ hS hv (hr p hp)).2.trans
      exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ h)
    · apply (kernel_ceiling m _ _ _ _ hS hv (hr p hp) hE).trans
      exact mul_le_mul (by linarith) (pow_le_pow_of_le_one (by positivity) (le_of_not_ge h) hD) (by positivity) (by linarith)
  have hl p : raw E p ≤ E⁻¹ := by
    apply inv_anti₀ hE
    nlinarith [sq_nonneg p]
  have hh : directLap E f ≤ tally 0 f * E⁻¹ := by
    rw [counts]; simp only [pow_zero,one_mul]; rw [← integral_mul_const]
    exact integral_mono (hf.paid (raw_c hE)) (f.integrable.mul_const E⁻¹) (fun p => mul_le_mul_of_nonneg_left (hl _) (hg p))
  calc
    _ ≤ _ := lamp_top m s f E hS hf hg hE _ hu
    _ ≤ 2*E*(tally 0 f*E⁻¹)*((1+kernelPrice m)*(s/E)^D) := by gcongr
    _ = _ := by field_simp

/-- Shape bounded below near zero. Using just this particular shape in the
final weighted estimates, integrates all dyads incl the E=0 endpoint. -/
private def ball_center : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
def center : Profile := ball_center.hasCompactSupport.toSchwartzMap ball_center.contDiff
lemma center_ends : Ends center := ball_center.hasCompactSupport
lemma center_plus : Plus center := fun _ => ball_center.nonneg
lemma center_even : Reflects false center := fun x => ball_center.neg x
lemma center_plane (p : ℝ) (hp : |p| ≤ 1) : center p=1 := ball_center.one_of_mem_closedBall (by
  rw [mem_closedBall]; exact (show dist p 0 ≤ 1 by simpa using hp))

lemma raw_bottom (w E : ℝ) (hw : 0<w) (he : 0<E) : (E+w)⁻¹ ≤ 2*E*directLap E (width w center) := by
  let d := w*E/(E+w)
  have hd : 0<d := by unfold d; positivity
  have hD : d≤w := by unfold d; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hl : d≤E := by unfold d; rw [div_le_iff₀ (by positivity)]; nlinarith
  let L : Set ℝ := Ioc 0 d
  let C := w⁻¹*(2*E^2)⁻¹
  let f (p) := width w center p * raw E p
  have hf : Integrable f := (Ends.width center_ends w).paid (raw_c he)
  have hh : (∫ _ in L,C) ≤ directLap E (width w center) := by
    apply le_trans (b:=∫ p in L,f p) ?_ (setIntegral_le_integral hf (ae_of_all _ fun p =>
      mul_nonneg (center_plus.tall _ hw.le _) (raw_n ..)))
    refine setIntegral_mono_on (integrableOn_const ?_) hf.integrableOn measurableSet_Ioc fun p hp => ?_
    · exact (lt_of_le_of_lt (measure_mono Ioc_subset_Icc_self) (isCompact_Icc.measure_lt_top (μ:=volume))).ne
    unfold f; rw [width_at,center_plane (p/w),mul_one]
    · have hv : p ≤ E := hp.2.trans hl
      have hr : 0<p := hp.1
      unfold C raw
      gcongr
      linarith [sq_le_sq₀ hr.le he.le |>.mpr hv]
    · have hv : p≤w := hp.2.trans hD
      have hr : 0<p := hp.1
      rw [abs_of_pos (by positivity),div_le_one hw]; exact hv
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hh (by positivity))
  dsimp only [L,C]
  rw [setIntegral_const,Real.volume_real_Ioc]
  rw [sub_zero,max_eq_left hd.le,smul_eq_mul]
  unfold d; field_simp

/-- Kernel bounded below by c/(w+E) even at zero, gaining inverse weights all the way
through the small energy range. (At high energy, include subtraction decay.) -/
lemma lower (m : ℕ) (s w E) (hs : 1≤s) (hw : 0<w) (hr : Room (width w center) s) (hE : 0≤E) :
    (2:ℝ)⁻¹^m * (E+w)⁻¹ * ((1+E)⁻¹)^(2*m) ≤ Mlamp m s (width w center) E := by
  let f (E : ℝ) := (2:ℝ)⁻¹^m * (E+w)⁻¹ * ((1+E)⁻¹)^(2*m)
  have hp (E : ℝ) (he : 0<E) : f E ≤ Mlamp m s (width w center) E := by
    refine le_trans ?_ (lamp_bottom m s _ E (by linarith) (Ends.width center_ends w) (center_plus.tall _ hw.le) he
      ((2:ℝ)⁻¹^m*(1+E)⁻¹^(2*m)) fun p hj v hv => kernel_floor _ _ _ _ _ hs hv (hr p hj) he)
    unfold f; rw [mul_comm ((2:ℝ)⁻¹^m),mul_assoc]
    exact mul_le_mul_of_nonneg_right (raw_bottom w E hw he) (by positivity)
  rcases eq_or_lt_of_le hE with rfl|he
  · have hv : ContinuousAt f 0 := by unfold f; fun_prop (disch:= positivity)
    refine le_of_tendsto_of_tendsto (to_zero _ hv.continuousWithinAt) (to_zero _ (Mlamp_cont m _ _ 0 self_mem_Ici)) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht; exact hp t ht
  exact hp E he

theorem Lap_meas (b : ℂ) (f : Form) : Measurable (Lap b f) :=
  ((damped_m b f).stronglyMeasurable.integral_prod_left' (μ:=volume)).measurable
lemma lamp_m (m s f) : Measurable (Mlamp m s f) := Complex.measurable_re.comp (Lap_meas _ _)
lemma tally_nn (f : Profile) (h : Plus f) : 0 ≤ tally 0 f := by rw [counts]; simp only [pow_zero,one_mul]; exact integral_nonneg h

theorem shelf (m D : ℕ) (hl : D≤2*m) (f : Profile) (hf : Ends f) (hg : Plus f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1≤s → ∀ w : ℝ, 0<w → Room (width w f) s → ∀ E : ℝ, 0≤E →
      Mlamp m s (width w f) E ≤ C*(w⁻¹+s^D)*((1+E)⁻¹)^D := by
  let Q := SchwartzMap.seminorm ℝ 0 0 f
  have hQ : 0 ≤ Q := apply_nonneg _ _
  let L := Q*(2*Real.pi)
  let H := (1+kernelPrice m)*(2*tally 0 f)
  have hL : 0 ≤ L := mul_nonneg hQ (by positivity)
  have hk := kernel_price_pos m
  have hH : 0 ≤ H := mul_nonneg (by positivity) (mul_nonneg (by positivity) (tally_nn f hg))
  refine ⟨max L H * 2^D,mul_nonneg (le_max_of_le_left hL) (by positivity),fun s hs w hw hr E he => ?_⟩
  have hu1 := Plus.tall hg w hw.le
  have hu := Ends.width hf w
  rcases le_total E 1 with hv|hv
  · refine le_trans (upper m s (width w f) E (by linarith) hu hu1 he hr (w⁻¹*Q) fun p => ?_) ?_
    · rw [width_at]; exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (f.norm_le_seminorm ℝ _)) (inv_pos.mpr hw).le
    · have ht : (1:ℝ) ≤ 2^D * ((1+E)⁻¹)^D := by
        rw [← mul_pow]
        refine one_le_pow₀ ?_
        rw [← div_eq_mul_inv]; exact (one_le_div (by linarith)).mpr (by linarith)
      calc
        _ = L*w⁻¹*1 := by dsimp only [L]; ring
        _ ≤ (max L H*(w⁻¹+s^D))*(2^D*((1+E)⁻¹)^D) := mul_le_mul
            (mul_le_mul (le_max_left ..) (le_add_of_nonneg_right (pow_nonneg (by linarith) _))
              (inv_pos.mpr hw).le (le_max_of_le_left hL)) ht zero_le_one (by positivity)
        _ = _ := by ring
  · have ht := off _ _ _ hs hu hu1 hr E hv D hl
    rw [tally_width 0 _ hw] at ht; simp only [pow_zero,one_mul] at ht
    apply ht.trans
    have hh : s/E ≤ s*2*(1+E)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    change H*_ ≤ _
    have hx : 0<s := by linarith
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤s/E by positivity) hh D) hH).trans
    simp only [mul_pow]
    calc
      _ = H * 2^D * s^D * ((1+E)⁻¹)^D := by ring
      _ ≤ _ := by gcongr; · exact le_max_right ..
                  exact le_add_of_nonneg_left (by positivity)
open OS Row
variable {G : Gauge} {L : Register G} {S : Table L} {i : Axis} (V : Chamber S i)

theorem surface (H : S.Hierarchy) (A : Weight L) (h : Pressed i A) (j : Axis) (hj : j≠i) (k : ℕ) :
    ∃ D : ℕ, ∀ (m : ℕ), D≤2*m → ∀ (f : Profile), Ends f → Plus f →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1≤s → ∀ w : ℝ, 0<w → Room (width w f) s →
        let g := fun p : E4 => Mlamp m s (width w f) (p i) * ‖p j‖^(2*k)
        Integrable g (ν V A) ∧ (∫ p, g p ∂ν V A) ≤ C*(w⁻¹+s^D) := by
  obtain ⟨D,hD⟩ := pay_moment V H A h j hj k
  let μ := ν V A
  let M (p : E4) := ((1+p i)⁻¹)^D * ‖p j‖^(2*k)
  have hu : ∀ᵐ p : E4 ∂μ, 0≤p i := before V A
  have hz : 0 ≤ ∫ p,M p ∂μ := integral_nonneg_of_ae (hu.mono fun x hx => show 0 ≤ ((1+_)⁻¹)^D * ‖x j‖^(2*k) by positivity)
  refine ⟨D,fun m hm f hf hp => ?_⟩
  obtain ⟨B,hB,hh⟩ := shelf m D hm f hf hp
  refine ⟨B*(∫ p,M p ∂μ),mul_nonneg hB hz,fun s hs w hw hr => ?_⟩
  intro g
  let c := B*(w⁻¹+s^D)
  have he : ∀ᵐ p ∂μ,g p≤c*M p := hu.mono (fun x hx =>
    (mul_le_mul_of_nonneg_right (hh s hs w hw hr (x i) hx) (pow_nonneg (norm_nonneg _) _)).trans_eq (mul_assoc ..))
  have hM : Integrable (fun p => c*M p) μ := hD.const_mul c
  have hg : Integrable g μ := by
    apply hM.mono'
    · have hv := lamp_m m s (width w f); unfold g; apply Measurable.aestronglyMeasurable; fun_prop
    filter_upwards [hu,he] with x hx hy
    rwa [Real.norm_of_nonneg (mul_nonneg (lamp_sign m s (width w f) (x i) (by linarith) hx (hf.width w) (hp.tall w hw.le) hr) (pow_nonneg (norm_nonneg _) _))]
  exact ⟨hg,(integral_mono_ae hg hM he).trans_eq (by rw [integral_const_mul]; exact mul_right_comm ..)⟩
end YM.Outer
