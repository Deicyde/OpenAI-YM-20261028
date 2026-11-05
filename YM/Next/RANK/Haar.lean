import YM.Gauge.Size
import YM.LocalH.Haar


/-!
# Integration costs with actual colour dimension

Both uses of  require the same exponent from small neighborhoods of
identity. The ambient matrix dimension packing bound for the lower bound
might lose an unbounded price at every site. Constants below depend only on
the gauge; don't scale with depth or period. We include even a disconnected
group and don't assume positive dimensionality. `shell` uses the normalized
chord, `order` integrals elsewhere will use exactly this probability Haar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank
open MeasureTheory Function Filter Set Metric Asymptotics Precision
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ENNReal

variable (G : Gauge)

lemma metric_law : ∀ᶠ x in 𝓝 (0:G.Color),
    ‖x‖/2 ≤ G.chord (G.lieExp x) ∧ G.chord (G.lieExp x) ≤ 2*‖x‖ := by
  let c := G.colorScale
  have hp : 0<c := G.colorScale_pos
  filter_upwards [G.expDiff_zero.isLittleO.def (half_pos hp)] with x H
  simp only [sub_zero,G.mat_lieExp_zero,G.mat_one] at H
  change ‖G.mat (G.lieExp x)-1-G.colorMat x‖ ≤ _ at H
  let A := ‖G.mat (G.lieExp x)-1‖
  have hv : |A-c*‖x‖| ≤ c/2 * ‖x‖ := by rw [show c*‖x‖= ‖G.colorMat x‖ from (G.colorMat_norm x).symm]; exact (abs_norm_sub_norm_le _ _).trans H
  obtain ⟨h₁,h₂⟩ := abs_le.mp hv
  change ‖x‖/2 ≤ A/c ∧ A/c ≤ 2*‖x‖
  rw [le_div_iff₀ hp,div_le_iff₀ hp]
  constructor <;> linarith only [h₁,h₂,mul_nonneg hp.le (norm_nonneg x)]

lemma surrounds (s : Set G.El) (h : s ∈ 𝓝 (1:G.El)) : ∃ R : ℝ,0<R ∧ G.shell R ⊆ s := by
  have hg := G.continuous_mat.isClosedEmbedding G.mat_injective
  rw [hg.isEmbedding.isInducing.nhds_eq_comap 1] at h
  obtain ⟨x,hx,h⟩ := mem_comap.mp h
  obtain ⟨r,hr,H⟩ := Metric.mem_nhds_iff.mp hx
  have hp := G.colorScale_pos
  refine ⟨(r/2)/G.colorScale,by positivity, fun i hi => h (mem_preimage.mpr (H ?_))⟩
  rw [mem_ball,dist_eq_norm,G.mat_one]
  change ‖_‖/G.colorScale ≤ _ at hi
  exact ((div_le_div_iff_of_pos_right hp).1 hi).trans_lt (half_lt_self hr)

private theorem color_vol (r : ℝ) (hr : 0<r) : volume (ball (0:G.Color) r) =
    ENNReal.ofReal (r^G.lieDim) * volume (ball (0:G.Color) 1) := by
  rw [Measure.addHaar_ball_of_pos volume _ hr, G.colorIso.finrank_eq]

private lemma inside : ∃ d : ℝ, 0<d ∧ d≤1 ∧ ∃ a b : ℝ, 0<a ∧ 0<b ∧ ∀ r : ℝ, 0<r → r≤d →
    a * r^G.lieDim ≤ G.probHaar.real (G.shell r) ∧ G.probHaar.real (G.shell r) ≤ b * r^G.lieDim := by
  obtain ⟨X,hX⟩ := LocalH.actual G
  let c := X.scale
  let B := ball (0:G.Color) X.radius
  let F := fun x : G.Color => ENNReal.ofReal (c * X.J x)
  have hc : 0 < c := hX.scale
  have h0 : (0:G.Color)∈ B := mem_ball_self hX.patch
  have ht : ∀ᶠ x in 𝓝 0, c/2 ≤ c*X.J x ∧ c*X.J x ≤ 2*c := by
    have he : ContinuousAt (fun x => c * X.J x) 0 := continuousAt_const.mul (hX.germ 0 h0).continuousAt
    filter_upwards [he.tendsto.eventually (Ioo_mem_nhds (a:= c/2) (b:=2*c) (by rw [hX.anchored,mul_one]; linarith) (by rw [hX.anchored,mul_one]; linarith))]
      with v hv using ⟨hv.1.le,hv.2.le⟩
  obtain ⟨z,hz,H⟩ := Metric.mem_nhds_iff.mp ((ht.and (metric_law G)).and (show ∀ᶠ x in 𝓝 0,x∈ B from isOpen_ball.mem_nhds h0))
  obtain ⟨V,hV,HV⟩ := LocalH.geom_patch G
  let r₀ := min z V
  let Z := ball (0:G.Color) r₀
  let T := G.lieExp '' B
  have hp : 0<r₀ := lt_min hz hV
  have ha (x : G.Color) (hx : x∈ Z) : c/2 ≤ c*X.J x ∧ c*X.J x ≤ 2*c := (H (ball_subset_ball (min_le_left z V) hx)).1.1
  have hg (x : G.Color) (hx : x∈ Z) : ‖x‖/2 ≤ G.chord (G.lieExp x) ∧ G.chord (G.lieExp x) ≤ 2*‖x‖ := (H (ball_subset_ball (min_le_left z V) hx)).1.2
  have hs : Z ⊆ B := fun _ hx => (H (ball_subset_ball (min_le_left z V) hx)).2
  obtain ⟨R,hR,HR⟩ := surrounds G (G.lieExp '' Z) ((HV r₀ (min_le_right ..)).1.mem_nhds
    (show (1:G.El) ∈ G.lieExp '' Z from ⟨0,mem_ball_self hp,G.mat_lieExp_zero⟩))
  let d := min 1 (min r₀ R)
  have dpos : 0 < d := lt_min zero_lt_one (lt_min hp hR)
  let w := volume (ball (0:G.Color) 1)
  have hw : w < ⊤ := measure_ball_lt_top
  have hw' : 0 < w := isOpen_ball.measure_pos _ (nonempty_ball.mpr zero_lt_one)
  let D := G.lieDim
  let C := w.toReal
  have hC : 0 < C := ENNReal.toReal_pos hw'.ne' hw.ne
  refine ⟨d, dpos, min_le_left ..,(c/2)*(2⁻¹:ℝ)^D*C,(2*c)*(3:ℝ)^D*C,by positivity,by positivity,fun r hr he => ?_⟩
  have heR : r ≤ R := he.trans ((min_le_right ..).trans (min_le_right ..))
  have her : r ≤ r₀ := he.trans ((min_le_right ..).trans (min_le_left ..))
  let L := G.shell r
  let P := G.lieExp ⁻¹' L
  have hl : L ⊆ G.lieExp '' Z := fun i hi => HR (le_trans hi heR)
  have hL : MeasurableSet L := G.shell_meas r
  have hP : MeasurableSet P := G.lieExp_cont.measurable hL
  have eq : G.probHaar L = ∫⁻ a in P∩B, F a := by
    rw [show G.probHaar L=(G.probHaar.restrict T) L by rw [Measure.restrict_apply hL,
      inter_eq_left.mpr (hl.trans (image_mono hs))]]
    unfold T B
    rw [← hX.actual,Measure.map_apply G.lieExp_cont.measurable hL,
      withDensity_apply _ hP,Measure.restrict_restrict hP]
  have drop : ball (0:G.Color) (r/2) ⊆ Z := ball_subset_ball ((half_le_self hr.le).trans her)
  have lo : ball (0:G.Color) (r/2) ⊆ P∩B := by
    intro x hx
    have hv := (hg x (drop hx)).2
    refine ⟨?_,hs (drop hx)⟩
    change G.chord (G.lieExp x) ≤ _
    rw [mem_ball,dist_zero_right] at hx
    linarith
  have hZ : P ∩ B ⊆ Z := by
    rintro i ⟨hi,hi'⟩
    obtain ⟨y,hy,hy'⟩ := hl hi
    exact hX.inject (hs hy) hi' hy' ▸ hy
  have hi : P ∩ B ⊆ ball (0:G.Color) (3*r) := by
    intro x hx
    rw [mem_ball,dist_zero_right]
    have hu : G.chord (G.lieExp x)≤ r := hx.1
    linarith [(hg x (hZ hx)).1]
  have p1 : ENNReal.ofReal (c/2) * (ENNReal.ofReal ((r/2)^D) * w) ≤ G.probHaar L := by
    rw [eq,show ENNReal.ofReal (_^D)*w = volume (ball (0:G.Color) (r/2)) from (color_vol G _ (by positivity)).symm,
      ← Measure.restrict_apply_univ,← lintegral_const]
    apply le_trans (setLIntegral_mono' isOpen_ball.measurableSet (g:=F) ?_)
      (lintegral_mono' (Measure.restrict_mono lo le_rfl) le_rfl)
    exact fun i hx => ENNReal.ofReal_le_ofReal (ha i (drop hx)).1
  have p2 : G.probHaar L ≤ ENNReal.ofReal (2*c) * (ENNReal.ofReal ((3*r)^D)*w) := by
    rw [eq,show ENNReal.ofReal (_^D)*w = volume (ball (0:G.Color) (3*r)) from (color_vol G _ (by positivity)).symm,
      ← Measure.restrict_apply_univ, ← lintegral_const]
    apply le_trans (setLIntegral_mono' (hP.inter isOpen_ball.measurableSet) (f:=F) ?_)
      (lintegral_mono' (Measure.restrict_mono hi le_rfl) le_rfl)
    exact fun i hx => ENNReal.ofReal_le_ofReal (ha i (hZ hx)).2
  constructor
  · have hx := ENNReal.toReal_mono (measure_ne_top _ _) p1
    rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (by positivity)] at hx
    apply le_trans ?_ hx
    unfold D C; rw [div_eq_mul_inv r, mul_pow]; exact le_of_eq (by ring)
  have hfin : ENNReal.ofReal (2*c) * (ENNReal.ofReal ((3*r)^D)*w) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.ofReal_lt_top) (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top) hw)
  have hx := ENNReal.toReal_mono hfin.ne p2
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (by positivity)] at hx
  refine hx.trans_eq ?_; change 2*c * ((3*r)^D * C) = _
  rw [mul_pow]; unfold D; ring

/-- Real Haar bounds on small links with the same dimension. The lower bound needs a
bounded radius. At dimension zero the powers are `1`; use positive radii throughout. -/
theorem shell_volume : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ s : ℝ, 0<s →
    (s ≤ 1 → a * s^G.lieDim ≤ G.probHaar.real (G.shell s)) ∧
      G.probHaar.real (G.shell s) ≤ b * s^G.lieDim := by
  obtain ⟨d,hd,h',a,b,ha,hb,H⟩ := inside G
  let D := G.lieDim
  refine ⟨a*d^D,max b (d^D)⁻¹,by positivity,hb.trans_le (le_max_left ..),?_⟩
  intro s hs
  rcases le_total s d with h|h
  · refine ⟨fun _ => (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hs.le D)).trans (H s hs h).1,
      (H s hs h).2.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg hs.le D))⟩
    exact mul_le_of_le_one_right ha.le (pow_le_one₀ hd.le h')
  refine ⟨fun hb => ?_, measureReal_le_one.trans ?_⟩
  · calc
      _ ≤ a*d^D := mul_le_of_le_one_right (by positivity) (pow_le_one₀ hs.le hb)
      _ ≤ _ := ((H _ hd le_rfl).1).trans (measureReal_mono (fun x (hp : x∈ G.shell d) => le_trans hp h))
  calc
    (1:ℝ) = (d^D)⁻¹*d^D := (inv_mul_cancel₀ (pow_pos hd D).ne').symm
    _ ≤ (d^D)⁻¹*s^D := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le h D) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)

private lemma geo (d : ℕ) : Summable fun k : ℕ => (((k:ℝ)+1)^d) * Real.exp (-(k:ℝ)) := by
  let r := Real.exp (-1)
  have hr : ‖r‖ < 1 := by simp [r,Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_lt_one_iff]
  have he := ((summable_pow_mul_geometric_of_norm_lt_one d hr).comp_injective (show Function.Injective (fun n : ℕ => n+1) from fun _ _ h => Nat.add_right_cancel h)).mul_right r⁻¹
  refine he.congr fun n => ?_
  simp only [Function.comp_apply,Nat.cast_add_one,pow_succ]
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one, ← Real.exp_nat_mul]
  simp

/-- Tail also at the correct volume power. Use later with `t=g/c > 0`. -/
theorem integral_budget : ∃ a b : ℝ, 0 < a ∧ a ≤ 1 ∧ 1 ≤ b ∧
    (∀ r : ℝ, 0 < r → r ≤ 1 → a*r^G.lieDim ≤ G.probHaar.real (G.shell (r/4))) ∧
    (∀ t : ℝ, 0 < t → (∫ u, Real.exp (-(G.chord u/t)) ∂G.probHaar) ≤ b*t^G.lieDim) := by
  classical
  obtain ⟨a,b,ha,hb,h⟩ := shell_volume G
  let D := G.lieDim
  let A := a/4^D
  let F (k : ℕ) := ((k:ℝ)+1)^D*Real.exp (-(k:ℝ))
  let B := (∑' k : ℕ,F k) * b
  refine ⟨min A 1,max 1 B,lt_min (by dsimp [A]; positivity) zero_lt_one,min_le_right ..,le_max_left ..,?_,?_⟩
  · intro r hp he
    calc
      _ ≤ A*r^D := mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity)
      _ = a*(r/4)^D := by dsimp [A]; rw [div_pow]; simp only [div_eq_mul_inv]; ac_rfl
      _ ≤ _ := (h _ (by positivity)).1 (by linarith)
  intro t ht
  let P := Finset.range (Nat.floor (2/t) + 1)
  let S k := G.shell (((k:ℝ)+1)*t)
  let I (k : ℕ) := (S k).indicator fun _ => Real.exp (-(k:ℝ))
  have he (k : ℕ) : MeasurableSet (S k) := G.shell_meas _
  have pos (k : ℕ) (x : G.El) : 0 ≤ I k x := indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  have hi k : Integrable (I k) G.probHaar := (integrable_const _).indicator (he _)
  have hu (x : G.El) : Real.exp (-(G.chord x/t)) ≤ ∑ i ∈ P,I i x := by
    let k := Nat.floor (G.chord x/t)
    have hk : x∈S k := le_of_lt ((div_lt_iff₀ ht).mp (Nat.lt_floor_add_one _))
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => pos _ _) (show k ∈ P from ?_))
    · change _ ≤ (S k).indicator _ x
      rw [indicator_of_mem hk, Real.exp_le_exp]
      exact neg_le_neg (Nat.floor_le (div_nonneg (G.chord_nonneg x) ht.le))
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right (G.chord_le_two _) ht.le)))
  have hw := geo D
  have ha (k : ℕ) : (∫ x,I k x∂G.probHaar) ≤ F k * (b*t^D) := by
    unfold I
    rw [integral_indicator (he k),setIntegral_const, smul_eq_mul]
    have hh : G.probHaar.real (S k) ≤ b*(((k:ℝ)+1)*t)^D := (h _ (by positivity)).2
    refine (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le).trans_eq ?_; unfold F; rw [mul_pow]; ring
  calc
    _ ≤ ∫ x,(∑ k ∈ P,I k x)∂G.probHaar := integral_mono ((show Continuous (fun x => Real.exp (-(G.chord x/t))) from by fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_finsetSum _ fun k _ => hi k) hu
    _ ≤ (∑ k ∈ P,F k) * (b*t^D) := by rw [integral_finsetSum _ fun k _ => hi k, Finset.sum_mul]; exact Finset.sum_le_sum fun k _ => ha k
    _ ≤ (∑' k,F k) * (b*t^D) := mul_le_mul_of_nonneg_right (hw.sum_le_tsum _ fun _ _ => by dsimp [F]; positivity) (by positivity)
    _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right 1 B) (by positivity)

end YM.Next.Rank
