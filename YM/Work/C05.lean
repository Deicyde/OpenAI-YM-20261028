import Mathlib.Analysis.Complex.RemovableSingularity
import YM.Analysis.Polydisc
import YM.Bid.Corners
import YM.Shift.Osc
import YM.Spark.Limit


/-!
# The absolute-frequency identity on compact Schwartz tests

We vary the tested strict-contour values along a ray from zero in height space.
The exponential test has a slope limit in Schwartz topology; the contour
functionals have a common bound continuous at zero by the power/lines theory.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.C05
open Function Set Filter MeasureTheory Boundary LineDeriv
open scoped ContDiff Topology BigOperators FourierTransform InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma smooth_jets (f : ℝ × X → ℂ) (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × X => iteratedFDeriv ℝ j (fun x => f (p.1, x)) p.2) := by
  induction j with
  | zero => exact (continuousMultilinearCurryFin0 ℝ X ℂ).symm.contDiff.comp hf
  | succ j ih =>
    have h : ContDiff ℝ ∞ (fun p : ℝ × X => fderiv ℝ (iteratedFDeriv ℝ j (fun x => f (p.1, x))) p.2) := by
      refine ContDiff.fderiv ?_ contDiff_snd (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
      exact ih.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    simp_rw [iteratedFDeriv_succ_eq_comp_left]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => X) ℂ).symm.contDiff.comp h

lemma continuous_of_common_compact (g : ℝ → Probe X) (hg : ContDiff ℝ ∞ (fun p : ℝ × X => g p.1 p.2))
    {K : Set X} (hK : IsCompact K) (hs : ∀ t, support ⇑(g t) ⊆ K) : Continuous g := by
  refine continuous_iff_continuousAt.mpr fun t => (Probe.tendN _ _ _).mpr ?_
  intro i j ε hε
  let v (s : ℝ) (x : X) := ‖x‖^i • Spark.jet x j (g s - g t)
  have hj := (smooth_jets _ hg j).continuous
  change Continuous (fun p : ℝ × X => Spark.jet p.2 j (g p.1)) at hj
  have hj' : Continuous (fun p : ℝ × X => Spark.jet p.2 j (g t)) := hj.comp (continuous_const.prodMk continuous_snd)
  have hv : Continuous (Function.uncurry v) := by
    simp only [uncurry_def, v, map_sub]
    exact (continuous_snd.norm.pow _).smul (hj.sub hj')
  have hu x : Tendsto (Function.uncurry v) (𝓝 t ×ˢ 𝓝 x) (𝓝 0) := by
    have eq : uncurry v (t,x) = 0 := by
      change ‖x‖^i • Spark.jet x j (g t - g t) = 0; rw [sub_self, map_zero]; exact smul_zero (A := Spark.Air j X) (‖x‖^i)
    rw [← nhds_prod_eq, ← eq]; exact hv.tendsto _
  filter_upwards [Spark.packing v K hK (fun x _ => hu x) _ (half_pos hε)] with s hh
  apply lt_of_le_of_lt (b := ε/2) _ (half_lt_self hε)
  apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (half_pos hε).le
  intro x
  by_cases hx : x ∈ K
  · simpa [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) i), Spark.Jet]
      using (hh x hx).le
  have h0 : (⇑(g s - g t)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    have eqz (u : ℝ) : g u y = 0 := by by_contra! h; exact hy (hs u h)
    change g s y - g t y = 0
    rw [eqz, eqz, sub_zero]
  simp [Probe.vanish_j _ _ h0, (half_pos hε).le]

lemma smooth_exp_slope : ContDiff ℝ ∞ (dslope Complex.exp 0) := by
  apply ContDiff.restrict_scalars ℝ (𝕜' := ℂ)
  apply Differentiable.contDiff
  rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
  exact Complex.differentiable_exp.differentiableOn

/-- Multiplication by the linear exponential on a fixed compactly supported
input has slope (in Schwartz topology) given by the linear-coordinate multiplier. -/
lemma tendsto_exp_slope (d : X) (g : Probe X) (hg : HasCompactSupport ⇑g) (F : ℝ → Probe X)
    (hF : ∀ t x, F t x = Complex.exp (↑t * ↑(inner ℝ d x)) * g x) (s : ℝ) :
    Tendsto (slope F s) (𝓝[≠] s)
      (𝓝 ((SchwartzMap.smulLeftCLM ℂ (fun x => inner ℝ d x)) (F s))) := by
  let c (x : X) := (↑(inner ℝ d x) : ℂ)
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp (innerSL ℝ d).contDiff
  let l (p : ℝ × X) := dslope Complex.exp 0 ((↑p.1 - ↑s) * c p.2) * c p.2 * F s p.2
  have hl : ContDiff ℝ ∞ l := by
    refine ((smooth_exp_slope.comp ?_).mul (hc.comp contDiff_snd)).mul ((F s).smooth ⊤ |>.comp contDiff_snd)
    exact ((Complex.ofRealCLM.contDiff.comp contDiff_fst).sub contDiff_const).mul (hc.comp contDiff_snd)
  have hsub (t : ℝ) : support (fun x : X => l (t,x)) ⊆ tsupport g := by
    apply Subset.trans ?_ (subset_tsupport ⇑g)
    intro x hx
    contrapose hx
    simp only [notMem_support] at hx ⊢
    simp [l, hF, hx]
  let L (t : ℝ) : Probe X := (HasCompactSupport.of_support_subset_isCompact hg (hsub t)).toSchwartzMap (hl.comp (contDiff_const.prodMk contDiff_id))
  have eqL : L s = SchwartzMap.smulLeftCLM ℂ (fun x => inner ℝ d x) (F s) := by
    ext1 x
    have hd : HasTemperateGrowth (fun x => inner ℝ d x) := (innerSL ℝ d).hasTemperateGrowth
    rw [SchwartzMap.smulLeftCLM_apply_apply hd, Complex.real_smul]
    change l (s,x) = _
    simp [l, c, dslope_same, Complex.deriv_exp]
  rw [← eqL]; apply (((continuous_of_common_compact L hl hg hsub).tendsto s).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin (s := ({s}ᶜ : Set ℝ)) (a := s)] with t ht
  have hne : (↑(t-s) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (show t ≠ s from ht)
  ext1 x
  rw [slope_def_module]
  change l (t,x) = (t-s)⁻¹ • (F t x - F s x)
  rw [Complex.real_smul, Complex.ofReal_inv]
  apply mul_left_cancel₀ hne
  rw [← mul_assoc _ ((↑(t-s) : ℂ)⁻¹), mul_inv_cancel₀ hne, one_mul, Complex.ofReal_sub]
  have hd := sub_smul_dslope Complex.exp 0 (((t:ℂ) - (s:ℂ)) * c x)
  rw [sub_zero, smul_eq_mul, Complex.exp_zero] at hd
  dsimp only [l]; rw [hF, hF]; change
    ((t:ℂ) - s) * (dslope _ _ _ * c x * (Complex.exp (↑s * c x) * g x)) =
    Complex.exp (↑t * c x) * g x - Complex.exp (↑s * c x) * g x
  rw [show (↑t : ℂ) * c x = (t-s : ℂ) * c x + s*c x by ring, Complex.exp_add]
  linear_combination (Complex.exp (↑s * c x) * g x) * hd

lemma continuous_of_tendsto_slope (F : ℝ → Probe X) (g : ℝ → Probe X)
    (hg : ∀ t, Tendsto (slope F t) (𝓝[≠] t) (𝓝 (g t))) : Continuous F := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  rw [continuousAt_iff_punctured_nhds]
  have h := (((tendsto_id.mono_left nhdsWithin_le_nhds).sub (tendsto_const_nhds (x := t))).smul (hg t)).add
    (tendsto_const_nhds (x := F t))
  simpa only [id_eq, sub_smul_slope, vsub_eq_sub, sub_add_cancel, sub_self, zero_smul, zero_add] using h

variable {n : ℕ}

lemma clock_hat (y : Heights n) (g : Joint n) :
    Waves.clock y (Probe.hat g) =
      - Probe.hat ((SchwartzMap.smulLeftCLM ℂ (fun x => inner ℝ (dawn y) x)) g) := by
  let m := dawn y
  simp only [Waves.clock, smul_apply, lineDerivOpCLM_apply]
  change (-Complex.I) • ∂_{m} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Probe.collapse (𝓕 g)) = _
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv, SchwartzMap.lineDerivOp_fourier_eq]
  change (-Complex.I) • Probe.hat (_ • _) = -Probe.hat _
  rw [← map_smul, ← map_neg]
  congr 1
  ext1 x
  have ht (p : Points n) : HasTemperateGrowth (fun x => inner ℝ p x) := (innerSL ℝ p).hasTemperateGrowth
  have hu (p : Points n) : HasTemperateGrowth (fun x => inner ℝ x p) := ((innerSL ℝ).flip p).hasTemperateGrowth
  simp only [smul_apply, neg_apply, smul_eq_mul]
  rw [SchwartzMap.smulLeftCLM_apply_apply (hu _), SchwartzMap.smulLeftCLM_apply_apply (ht _)]
  simp only [Probe.shrinking,
    real_inner_smul_right, real_inner_comm m x, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  have hn : (Probe.q : ℂ) ≠ 0 := by exact_mod_cast Probe.qpos.ne'
  change _ = -(↑(inner ℝ m x) * g x)
  field_simp
  simp only [Probe.q, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (2 * ↑Real.pi * (inner ℝ m x : ℂ) * g x) * Complex.I_sq

variable {G : Gauge} {L : Register G} {S : Table L} (F : Waves S)
variable {v : Fin n → S.Union}

def psiL (h : F.Bounds) (v : Fin n → S.Union) (y : Heights n) (hy : y ∈ east n) : Joint n →ₗ[ℝ] ℂ where
  toFun := F.psi v y
  map_add' f g := by
    unfold Waves.psi; rw [← integral_add (h n v y hy f) (h n v y hy g)]
    congr 1; ext x; exact mul_add ..
  map_smul' a f := by
    change F.psi v y (a • f) = a • F.psi v y f
    unfold Waves.psi; rw [← integral_smul]; congr 1; ext x; exact mul_smul_comm a _ (f x)

lemma tendsto_psi (hb : F.Bounds) (ha : F.Along) (hl : F.Lines) (hp : F.Breathes)
    {Z : Type*} {l : Filter Z} {u : Z → Heights n} {g : Z → Joint n} {f : Joint n} {a : ℂ}
    (hu : ∀ᶠ t in l, u t ∈ east n) (hg : Tendsto g l (𝓝 f))
    (ht : Tendsto (fun t => F.psi v (u t) f) l (𝓝 a)) :
    Tendsto (fun t => F.psi v (u t) (g t)) l (𝓝 a) := by
  obtain ⟨m,C,_,hc⟩ := hp n v
  obtain ⟨h0,hcont⟩ := Waves.tolls (n := n) m C
  have htoll : Tendsto (fun t => Waves.toll (g t - f) C m) l (𝓝 0) := by
    rw [← h0]
    apply (hcont.tendsto 0).comp
    simpa using hg.sub (tendsto_const_nhds (x := f))
  have hh : Tendsto (fun t => F.psi v (u t) (g t - f)) l (𝓝 0) := by
    apply squeeze_zero_norm' ?_ htoll
    filter_upwards [hu] with t h
    rw [← F.meant ha hl _ _ h _ m]
    exact F.cost hc _ (bigger h) _
  rw [← zero_add a]
  apply (hh.add ht).congr'
  filter_upwards [hu] with t h
  change psiL F hb v (u t) h (g t - f) + F.psi .. = _
  rw [map_sub, show psiL F hb v (u t) h f = F.psi v (u t) f from rfl, sub_add_cancel]; rfl

lemma ray_mem {y : Heights n} (hy : y ∈ east n) {s : ℝ} (hs : 0 < s) : s • y ∈ east n :=
  fun _ _ hab => mul_lt_mul_of_pos_left (hy hab) hs

lemma hasDerivAt_zero_psi (hb : F.Bounds) (ha : F.Along) (hl : F.Lines) (hp : F.Breathes)
    (v : Fin n → S.Union) (y : Heights n) (hy : y ∈ east n) (f : ℝ → Joint n) (s : ℝ) (hs : 0 < s)
    (hd : Tendsto (slope f s) (𝓝[≠] s) (𝓝 (- Waves.clock y (f s)))) :
    HasDerivAt (fun t : ℝ => F.psi v (t • y) (f t)) 0 s := by
  have lines (g : Joint n) : HasDerivAt (fun t : ℝ => F.psi v (t • y) g)
      (F.psi v (s • y) (Waves.clock y g)) s := by
    simpa using hl n v g 0 y s (by simpa using ray_mem hy hs)
  have hu : ∀ᶠ t in 𝓝[≠] s, t • y ∈ east n := (eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds hs)).mono
    (fun _ h => ray_mem hy h)
  have H := tendsto_psi F hb ha hl hp hu hd ((lines (- Waves.clock y (f s))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [show F.psi v (s • y) (- Waves.clock y (f s)) = -(F.psi v (s • y) (Waves.clock y (f s))) from
    map_neg (psiL F hb v _ (ray_mem hy hs)) _] at H
  rw [hasDerivAt_iff_tendsto_slope, ← neg_add_cancel (F.psi v (s • y) (Waves.clock y (f s)))]
  apply (H.add (lines (f s)).tendsto_slope).congr'
  filter_upwards [hu] with t ht
  simp only [slope_def_module]
  change psiL F hb v _ ht _ + _ = _
  rw [map_smul, map_sub, smul_sub, smul_sub, smul_sub]
  change (t-s)⁻¹ • F.psi v _ _ - (t-s)⁻¹ • F.psi v _ _ + (_ - _) = _
  abel

/-- Absolute-coordinate strict height Fourier transform tested with compact
support after exponential multiplication; the original surface is kept. -/
theorem answer : YM.Bid.C05 := by
  intro G L S T F W _ hp hl ha hw n v y hy f hf
  let d := dawn y
  let K (t : ℝ) : Joint n := lifts (t • d) f hf
  let k := fun t => Probe.hat (K t)
  have hk (s : ℝ) : Tendsto (slope k s) (𝓝[≠] s) (𝓝 (-Waves.clock y (k s))) := by
    have he := tendsto_exp_slope d f hf K (by intro t x; simp [K, real_inner_smul_left]) s
    rw [clock_hat, neg_neg]
    apply (Probe.hat.continuous.continuousAt.tendsto.comp he).congr'
    exact Eventually.of_forall fun t => ((Probe.hat.restrictScalars ℝ).toLinearMap.slope_comp K s t).symm
  have hd s (hs : 0 < s) := hasDerivAt_zero_psi F hw.int ha hl hp v y hy k s hs (hk s)
  let A (s : ℝ) := F.psi v (s • y) (k s)
  have const t (ht : 0 < t) : A t = A 1 := by
    refine (convex_Ioi (𝕜 := ℝ) (0:ℝ)).is_const_of_fderivWithin_eq_zero
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt) (fun s hs => ?_) ht (show (0:ℝ)<1 from zero_lt_one)
    rw [fderivWithin_of_isOpen isOpen_Ioi hs, (hd s hs).hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_zero]
  have h0 : k 0 = Probe.hat f := by
    change Probe.hat (lifts _ f hf) = _
    congr 1; ext1 x; simp
  have hlim : Tendsto A (𝓝[>] 0) (𝓝 (W.W n v (k 0))) :=
    tendsto_psi F hw.int ha hl hp (Eventually.mono self_mem_nhdsWithin (fun t ht => ray_mem hy (show 0<t from ht)))
      (((continuous_of_tendsto_slope _ _ hk).tendsto 0).mono_left nhdsWithin_le_nhds) ((F.exposed W hw).profile n v y hy (k 0))
  rw [h0] at hlim
  have hu : Tendsto A (𝓝[>] 0) (𝓝 (A 1)) := tendsto_const_nhds.congr'
    (Eventually.mono self_mem_nhdsWithin (fun t ht => (const t (show 0<t from ht)).symm))
  simpa [A, k, K] using tendsto_nhds_unique hlim hu

-- Checks of absolute-variable convention in degenerate arities, independent of contour hypotheses.
example (y : Heights 0) (f : Joint 0) (h : HasCompactSupport ⇑f) :
    Probe.hat (lifts (dawn y) f h) = Probe.hat f := by
  congr 1; ext1 x
  rw [Subsingleton.elim (dawn y) 0]; simp

example (y : Heights 1) (p : Points 1) (f : Joint 1) (h : HasCompactSupport ⇑f) :
    lifts (dawn y) f h p = Complex.exp (y 0 * YM.time (p 0) : ℝ) * f p := by
  rw [rises, PiLp.inner_apply]; simp [dawn, place, YM.Mink.pairing]
end YM.Work.C05
