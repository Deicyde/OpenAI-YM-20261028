import YM.UVNext.UV_STATION_TRANSFER.Placement
import YM.UVNext.UV_STATION_TRANSFER.Quadrature


set_option warningAsError false

/-!
# Short for one probe word

The approximation uses the regulator lattice directly,
not an interpolation in a limiting hierarchy. At each station this is
order zero on *joint tests* in the whole rescaled window; threshold for
the error vs free QUADRATURE does not even depend on the test. As expected
threshold for error vs free INTEGRAL may depend on the test: uniform cost
doesn't mean uniform threshold beyond the quadrature.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.StationTransfer
open Function Set Filter MeasureTheory Measure Metric Analysis Extraction
open Extraction.Difference Lattice Wilson Climb Ward Table Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {D n : ℕ} {t : Caps n}

-- residual integrand in physical units
def rest (X : Wheel C D) (h : ∀ i,t i≤D) (w : Ribbon (Bel C.book) t) (f : Test n) (N p : ℕ) :=
  densityCell C N p (ripped (C:=C) (t:=t) (X.tones h w (N,p))) (dilate X.rad f) -
  integrand C (quoteFree (disc (hang t w)) X.rad f) N p

lemma diff (X : Wheel C D) (h : ∀ i,t i≤D) (w : Ribbon (Bel C.book) t) (f : Test n) (N p : ℕ) :
    X.paid (hang t w) h f N p - quadrature C (quoteFree (disc (hang t w)) X.rad f) N p = ∫ x,rest X h w f N p x := by
  unfold rest; simp only [Pi.sub_apply]
  rw [integral_sub (show Integrable (densityCell C N p (ripped (C:=C) (t:=t) (X.tones h w (N,p))) (dilate X.rad f)) volume from by unfold densityCell; apply stair_int _) (show Integrable (integrand C (quoteFree (disc (hang t w)) X.rad f) N p) volume from by unfold integrand; apply stair_int _),exactSmear,integral_eq]; rfl

lemma stepped_rest (X : Wheel C D) (h : ∀ i,t i≤D) (w : Ribbon (Bel C.book) t) (f : Test n) (N p : ℕ)
    (x : Points n) (hx : X.r • x ∈ Fund C.S p n) :
    let a : positions n := address (C.S.a N) (X.r • x); let y := fine X N a
    ((X.r^(4*n):ℝ):ℂ)*rest X h w f N p (X.r • x) =
      f y * (revenue X h w N p a - disc (hang t w) y) := by
  intro a y
  rw [rest,Pi.sub_apply,stepped C _ p hx,integrand,stair, indicator_of_mem hx,corner_tag C hx]
  unfold quoteFree
  rw [← physical_tag X]; change ((X.r^(4*n):ℝ):ℂ) *
    ((↑((X.r^(4*n))⁻¹):ℂ)*f (X.r⁻¹ • (X.r • y)) * revenue X h w N p a -
     (↑((X.r^(4*n))⁻¹):ℂ) * f (X.r⁻¹ • (X.r • y)) * disc (hang t w) (X.r⁻¹ • (X.r • y))) = _
  rw [inv_smul_smul₀ X.rad.ne']
  have he : (↑(X.r^(4*n)):ℂ) * (↑((X.r^(4*n))⁻¹):ℂ)=1 := by
    rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (pow_pos X.rad _).ne')]
  linear_combination (norm := ring) (f y * (revenue X h w N p a - disc (hang t w) y)) * he

lemma rest_scaled (X : Wheel C D) (h : ∀ i,t i≤D) (w : Ribbon (Bel C.book) t) (f : Test n) (N p : ℕ) :
    (∫ x : Points n, rest X h w f N p x) = ∫ x : Points n, (↑(X.r^(4*n)):ℂ)*rest X h w f N p (X.r • x) := by
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume _ X.r (hR:=X.rad.le),
    point_dimension, Complex.real_smul]
  simp [X.rad.ne']

lemma rest_bound (X : Wheel C D) (h : ∀ i,t i≤D) (w : Ribbon (Bel C.book) t)
    {R κ A α M c : ℝ} (hr : 0<R) (hc : 0≤c) (hA : 0≤A) (ha : 0≤α) (hM : 0≤M)
    (hQ : ∀ x∈Scaling.window R n, ‖disc (hang t w) x‖ ≤ c)
    (hW : cthickening κ (Scaling.window R n) ⊆ Scaling.window (2*R) n)
    {N p : ℕ} (hf : (4*n:ℝ)*C.S.a N ≤ X.r*min κ X.σ)
    (hx : ∀ u : positions n, fine X N u∈Scaling.window R n → ‖revenue X h w N p u‖ ≤ A^n)
    (he : ∀ u : positions n, fine X N u∈Scaling.window R n → fine X N u∈openFilm n (8*X.σ) →
      ‖revenue X h w N p u - disc (hang t w) (fine X N u)‖ ≤ α)
    (f : Test n) (hp : tsupport f ⊆ Scaling.window R n) (hB : ∀ x, ‖f x‖ ≤ M) :
    ‖∫ x, rest X h w f N p x‖ ≤ M*(α*volume.real (Scaling.window (2*R) n)+
      (A^n+c)*(cost_band n (2*R)*(2*X.σ))) := by
  classical
  let W := Scaling.window (2*R) n
  let B := W \ openFilm n (8*(2*X.σ))
  have hm : MeasurableSet W := (window_closed ..).measurableSet
  have hh : volume W < ⊤ := (window_closed ..).measure_lt_top
  have hb : MeasurableSet B := hm.diff (open_film _).measurableSet
  have hv : volume B < ⊤ := (measure_mono (show B ⊆ W from sdiff_subset)).trans_lt hh
  let P := W.indicator fun _ => M*α; let Q := B.indicator fun _ => M*(A^n+c)
  have hP : Integrable P := (integrable_indicator_iff hm).2 (integrableOn_const hh.ne)
  have hq : Integrable Q := (integrable_indicator_iff hb).2 (integrableOn_const hv.ne)
  have hZ : 0 ≤ A^n+c := by positivity
  have ht (x) : 0 ≤ Q x := indicator_nonneg (fun _ _ => mul_nonneg hM hZ) x
  have ht' (x) : 0 ≤ P x := indicator_nonneg (fun _ _ => mul_nonneg hM ha) x
  have hs := X.stripe
  rw [rest_scaled]
  refine (norm_integral_le_of_norm_le (hP.add hq) ?_).trans ?_
  · filter_upwards with x
    rw [Pi.add_apply]
    by_cases hu : X.r • x∈Fund C.S p n
    · let u := address (C.S.a N) (X.r • x); let y := fine X N u
      rw [stepped_rest X h w f N p x hu]
      change ‖f y * _‖ ≤ _
      by_cases hi : f y=0
      · rw [hi,zero_mul,norm_zero]; exact add_nonneg (ht' _) (ht _)
      have hY := hp (subset_closure (show y∈support f from hi))
      have HD : dist x y ≤ min κ X.σ := by
        apply le_of_mul_le_mul_left _ X.rad
        rw [← real_stretch X.rad.le,dist_comm]
        exact (physical_tag X N u ▸ approximate (C.S.a_pos N) (X.r • x) : -- maybe rewrite orientation
          dist (X.r • y) (X.r • x) ≤ _).trans hf
      have H : x∈W := hW (mem_cthickening_of_dist_le _ y _ _ hY (HD.trans (min_le_left ..)))
      rw [show P x=M*α from indicator_of_mem H _, norm_mul]
      by_cases hy : y∈openFilm n (8*X.σ)
      · exact (mul_le_mul (hB y) (he u hY hy) (norm_nonneg _) hM).trans (le_add_of_nonneg_right (ht _))
      have HZ : x∈B := ⟨H,fun hx' => hy (show y∈openFilm n (8*X.σ) from by
        have HH : y∈closedBall x (2*X.σ) := by
          rw [dist_comm] at HD; exact HD.trans ((min_le_right ..).trans (by linarith))
        convert closed_thin (by linarith : 0 ≤ 2*X.σ) x hx' HH using 1
        ring_nf)⟩
      rw [show Q x=M*(A^n+c) from indicator_of_mem HZ _]
      exact (mul_le_mul (hB y) ((norm_sub_le ..).trans (add_le_add (hx u hY) (hQ _ hY))) (norm_nonneg _) hM).trans
        (le_add_of_nonneg_left (mul_nonneg hM ha))
    unfold rest integrand densityCell stair
    rw [Pi.sub_apply,indicator_of_notMem hu,indicator_of_notMem hu,sub_zero,mul_zero,norm_zero]; exact add_nonneg (ht' _) (ht _)
  simp only [Pi.add_apply]; rw [integral_add hP hq]
  unfold P Q; rw [integral_indicator hm,setIntegral_const, integral_indicator hb,setIntegral_const]
  have he := mul_le_mul_of_nonneg_right (band_cover (2*R) (by linarith) (2*X.σ) (by linarith) (n:=n)) (mul_nonneg hM hZ)
  calc
    _ ≤ volume.real W * (M*α) + (cost_band n (2*R)*(2*X.σ))*(M*(A^n+c)) := add_le_add_right he _
    _ = _ := by unfold W; ring

lemma compares_quadrature (W : ℕ→Wheel C D) (h : ∀ i,t i≤D) (w : Ribbon (Bel C.book) t)
    (hm : (Bel C.book).Smooth) {R : ℝ} (hr : 0<R) {A : ℕ→ℝ} (hp : PlacementPrices W F R h w A) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop, F.late fun N p =>
      ∀ f : Test n, tsupport f ⊆ Scaling.window R n → ∀ M : ℝ,0≤M → (∀ x, ‖f x‖ ≤ M) →
      ‖(W k).paid (hang t w) h f N p - quadrature C (quoteFree (disc (hang t w)) (W k).rad f) N p‖ ≤ ε*M := by
  intro ε he
  let K := Scaling.window R n
  let V := volume.real (Scaling.window (2*R) n)
  let Q := disc (hang t w)
  obtain ⟨κ,hκ,hW⟩ := upgrade_window (n:=n) R hr
  obtain ⟨y,hy⟩ := ((window_closed R n).image_of_continuousOn
    (((smoothDisc hm _).continuousOn (f:=Q)).mono (show K ⊆ conf n from fun _ hx =>
      spaced_conf (inv_pos.mpr hr) hx.1) |>.norm)).bddAbove
  let c := max y 0
  have hc : 0≤c := le_max_right ..
  have ht : Tendsto (fun k => (A k^n+c)*(cost_band n (2*R)*(2*(W k).σ))) atTop (𝓝 0) := by
    have hZ := (hp.rose.add (hp.ties.const_mul c)).mul_const (cost_band n (2*R)*2)
    rw [mul_zero,add_zero,zero_mul] at hZ; exact hZ.congr fun k => by ring
  have hv : 0<1+V := add_pos_of_pos_of_nonneg zero_lt_one ENNReal.toReal_nonneg
  let α := (ε/2)/(1+V)
  have hA : 0<α := div_pos (half_pos he) hv
  filter_upwards [hp.whole,hp.away α hA,ht.eventually (ge_mem_nhds (half_pos he))] with k hk hx hB
  unfold Extraction.Order.late at *
  have hF : 0 < (W k).r * min κ (W k).σ := mul_pos (W k).rad (lt_min hκ (W k).stripe)
  have hN : Tendsto (fun N => (4*n:ℝ)*C.S.a N) atTop (𝓝 0) := by simpa using C.S.shrinks.const_mul (4*n:ℝ)
  filter_upwards [hk.2,hx] with i hi hv'
  filter_upwards [hi,hv',F.mesh.cofinal.eventually (hN.eventually (ge_mem_nhds hF))] with j hj he' hg f hS M hM hf
  rw [diff]; apply le_trans (rest_bound (W k) h w hr hc hk.1 hA.le hM (fun i hi => le_trans
    (hy (mem_image_of_mem _ hi)) (le_max_left ..)) hW hg hj he' _ hS hf)
  rw [mul_comm ε]; apply mul_le_mul_of_nonneg_left _ hM
  have hh : α*V≤ε/2 := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hA.le).trans
    (show α*(1+V) ≤ ε/2 from by unfold α; rw [div_mul_cancel₀ _ hv.ne'])
  exact (add_le_add hh hB).trans_eq (add_halves _)

-- remove free quadrature with threshold per f
theorem short_word (W : ℕ→Wheel C D) (h : ∀ i,t i≤D) (w : Ribbon (Bel C.book) t)
    (hm : (Bel C.book).Smooth) {R : ℝ} (hr : 0<R) {A : ℕ→ℝ} (hp : PlacementPrices W F R h w A) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop, ∀ f : Test n, tsupport f ⊆ Scaling.window R n →
      ∀ M : ℝ, 0 < M → (∀ x, ‖f x‖ ≤ M) → F.upper
      (fun N p => ‖(W k).paid (hang t w) h f N p-f.applyTo (disc (hang t w))‖) (M*ε) := by
  intro ε he
  filter_upwards [compares_quadrature W h w hm hr hp ε he] with k hk f hf M hM hT η hη
  let Q := disc (hang t w)
  let Z := quadrature C (quoteFree Q (W k).rad f)
  have hi := Metric.tendsto_nhds.mp (quadrature_quoted C F _ (smoothDisc (T:=Bel C.book) hm (hang t w)).continuousOn (W k).rad f) η hη
  rw [Extraction.Order.fused] at hi
  unfold Extraction.Order.late at hi hk ⊢
  filter_upwards [hi,hk] with i hy ha
  filter_upwards [hy,ha] with j hy ha
  change dist (Z _ _) _ < η at hy
  rw [← dist_eq_norm]
  let B := (W k).paid (hang t w) h f (F.mesh j) (F.per i)
  have ht : dist B (Z (F.mesh j) (F.per i)) ≤ M*ε := by rw [dist_eq_norm,mul_comm]; exact ha f hf M hM.le hT
  exact (dist_triangle B (Z _ _) _).trans (add_le_add ht hy.le)

end YM.UVNext.StationTransfer
