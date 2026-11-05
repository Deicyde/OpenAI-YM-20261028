import YM.UVNext.FREE_STRESS_CERTIFICATE.LocalCross

/-!
# Normalize the single-contraction Maxwell cross stress through the
actual Green. Translation weight first. Only mollify the enclosed leg.
No identification/leap from bulk to boundary without off-pole limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Set MeasureTheory Filter Analysis Function
open scoped Topology ContDiff

variable {U : Set E4} (u : Maxwell.Field ℝ) (h : WaveOn U u) (ht : IsOpen U)

-- cutoff tools for native real kernels
private lemma patched {f g : E4 → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hG : ∀ x∈ tsupport f, ContDiffAt ℝ ∞ g x) :
    ContDiff ℝ ∞ (f*g) ∧ HasCompactSupport (f*g) := by
  refine ⟨contDiff_iff_contDiffAt.mpr fun x => ?_, hc.mul_right⟩
  by_cases he : x ∈ tsupport f
  · exact hf.contDiffAt.mul (hG x he)
  refine (contDiffAt_const (𝕜:=ℝ) (c:=(0:ℝ)) (x:=x)).congr_of_eventuallyEq ?_
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp he] with i hi
  exact mul_eq_zero_of_left hi _

private lemma different {g : E4 → ℝ} {x} (he : ContDiffAt ℝ ∞ g x) (a : Axis) : ContDiffAt ℝ ∞ (grad a g) x := grad_smooth a he (by simp)
private lemma prepared_D {g : E4 → ℝ} (he : ContDiff ℝ ∞ g) (a : Axis) : ContDiff ℝ ∞ (grad a g) :=
  contDiff_iff_contDiffAt.mpr fun _ => different he.contDiffAt _

private theorem side {f g : E4→ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hG : ∀ x∈ tsupport f, ContDiffAt ℝ ∞ g x)
    (a : Axis) :
    Integrable (fun y => f y * grad a g y) ∧ Integrable (fun y => grad a f y * g y) ∧ Integrable (fun y => f y*g y) ∧
      ((∫ y, f y * grad a g y) = -∫ y, grad a f y * g y) := by
  have H {f g : E4→ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hG : ∀ x ∈ tsupport f, ContDiffAt ℝ ∞ g x) : Integrable fun y => f y*g y :=
    (patched hf hc hG).1.continuous.integrable_of_hasCompactSupport hc.mul_right
  have he := H hf hc (fun x hx => different (hG x hx) a)
  have hr := H (prepared_D hf a) (hc.fderiv_apply ℝ _) (fun x hx => hG x (tsupport_fderiv_apply_subset ℝ _ hx))
  exact ⟨he,hr,H hf hc hG,integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (𝕜:=ℝ) (G:=ℝ) (E:=E4) (μ:=volume)
    (f:=f) (g:=g) (v:=basis a) hr he (H hf hc hG) (fun x _ => hf.differentiable (by simp) _) (fun x hx => (hG _ hx).differentiableAt (by simp))⟩

private lemma droplet_smooth {r : ℝ} (h : r≠0) : ContDiff ℝ ∞ (droplet r) := by
  unfold droplet; exact contDiff_const.mul ((((contDiff_norm_sq ℝ).add contDiff_const).inv (fun x => denom_ready _ _ (Or.inl h))).pow _)

section center
variable (χ : E4→ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (ha : tsupport χ⊆U)
include h ht hχ hc ha

-- Integration identity valid even for other tests inside support (don't ask χ
-- equal 1 until translating to a number). Thus next step can take vector field
-- comparisons by twisting the test & removing Killing-derivative term.
private theorem pour {r : ℝ} (hp : r≠0) (i j b : Axis) :
    -(∑ a, ∫ x, grad a χ x * score r u i j a b x) =
      (-(∫ x, droplet r x * grad i (χ * u b j) x)) + ∫ x, droplet r x * grad j (χ * u b i) x := by
  have he (a : Axis) : ∀ x∈tsupport χ, ContDiffAt ℝ ∞ (score r u i j a b) x := fun x hx =>
    score_smooth r u h i j a b (ha hx) (Or.inl hp)
  have hh (a : Axis) := side hχ hc (he a) a
  simp_rw [← Finset.sum_neg_distrib, ← (hh _).2.2.2, ← integral_finsetSum _ (fun a _ => (hh a).1), ← Finset.mul_sum]
  have H (a b : Axis) := patched hχ hc (g:=u a b) (fun x hx => h.smooth a b x (ha hx))
  have hd (a b : Axis) (c) := side (H a b).1 (H a b).2 (fun _ _ => (droplet_smooth hp).contDiffAt) c
  have hp (x : E4) : χ x * (∑ a, grad a (score r u i j a b) x) =
      (χ * u b j) x * grad i (droplet r) x - (χ * u b i) x * grad j (droplet r) x := by
    by_cases hx : x ∈ tsupport χ
    · rw [score_div r u h ht (ha hx) hp]; change _ = χ x * _ * _ - χ x * _ * _; ring
    change _ = χ x * _ * _ - χ x * _ * _
    rw [image_eq_zero_of_notMem_tsupport hx]; ring
  simp_rw [hp, integral_sub (hd b j i).1 (hd b i j).1, (hd b j i).2.2.2,(hd b i j).2.2.2,
    mul_comm (droplet r _)]
  abel

-- `χ` now one in a neighborhood. Its derivative really vanishes there.
omit h ht hχ hc ha in
private lemma piece0 (hz : χ =ᶠ[𝓝 0] fun _ => 1) (a : Axis) : (0:E4) ∉ tsupport (grad a χ) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [hz.fderiv (𝕜:=ℝ)] with y hy
  simp [grad,D,hy]

omit ht in
private lemma late (hz : χ =ᶠ[𝓝 0] fun _ => 1) (i j a b : Axis) :
    Continuous (fun r => ∫ x, grad a χ x * score r u i j a b x) := by
  let f (r : ℝ) (x : E4) := grad a χ x * score r u i j a b x
  let A := tsupport (grad a χ)
  have hA : IsCompact A := hc.fderiv_apply ℝ _
  have hD (x : E4) : ContinuousAt (grad a χ) x := (different hχ.contDiffAt a).continuousAt
  have hf : Continuous (uncurry f) := by
    refine continuous_iff_continuousAt.mpr fun w => ?_
    obtain ⟨r,x⟩ := w
    by_cases he : x∈A
    · have he' := ha (tsupport_fderiv_apply_subset ℝ _ he)
      have hm (a b c d : Axis) : ContinuousAt (fun v : ℝ×E4 => material v.1 i j a b v.2*u c d v.2) (r,x) :=
        (jointly (fun hh => piece0 χ hz _ (hh ▸ he)) _ _ _ _).mul (((h.smooth c d x he').continuousAt).comp (x:=(r,x)) continuousAt_snd)
      apply ((hD x).comp (x:=(r,x)) continuousAt_snd).mul
        ((tendsto_finsetSum _ (fun c _ => (hm a c b c).add (hm b c a c))).sub ?_)
      by_cases ht : a=b
      · simp only [if_pos ht]; exact continuousAt_const.mul (tendsto_finsetSum _ (fun l _ => tendsto_finsetSum _ fun c _ => hm _ _ _ _))
      simp only [if_neg ht]; exact continuousAt_const
    apply ContinuousAt.congr_of_eventuallyEq (f:=fun _ => 0) continuousAt_const
    have hr := (notMem_tsupport_iff_eventuallyEq.mp he).comp_tendsto (continuousAt_snd (p:=(r,x))).tendsto
    filter_upwards [hr] with y hy
    change grad a χ y.2*_=0; rw [show grad a χ y.2=0 from hy,zero_mul]
  exact continuousOn_univ.mp (continuousOn_integral_of_compact_support hA hf.continuousOn fun _ y _ hy => by
    change grad a χ y*_=0; rw [image_eq_zero_of_notMem_tsupport hy,zero_mul])

/-- Exact single-contraction translation flux in one color, enclosed field
strength (Euler sign negative). -/
theorem single_cross (hz : χ =ᶠ[𝓝 0] fun _ => 1) (i j b : Axis) :
    -(∑ a, ∫ x, grad a χ x * crossing (fun a b => bareCurl a b i j x) (fun a b=> u a b x) a b) =
      -grad b (u i j) 0 := by
  let g (r : ℝ) := -(∑ a, ∫ x, grad a χ x * score r u i j a b x)
  have hg : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := ((continuous_finsetSum _ (fun a _ => late u h χ hχ hc ha hz i j a b)).neg.continuousAt.continuousWithinAt)
  have hi (i j k : Axis) := patched hχ hc (g:=u i j) (fun x hx => h.smooth i j x (ha hx))
  have he (i j k) : Tendsto (fun r => ∫ x, droplet r x * grad k (χ * u i j) x) (𝓝[>] 0) (𝓝 (grad k (u i j) 0)) := by
    have hh : (χ * u i j) =ᶠ[𝓝 0] (u i j) := by filter_upwards [hz] with y hy; change χ y*_=_; rw [show χ y=1 from hy,one_mul]
    rw [grad, ← GermD (basis k) hh]
    exact rains _ (prepared_D (hi i j k).1 _).continuous ((hi i j k).2.fderiv_apply _ _)
  have hq : g 0= -grad i (u b j) 0 + grad j (u b i) 0 := by
    refine tendsto_nhds_unique hg (Tendsto.congr' ?_ ((he b j i).neg.add (he b i j)))
    exact (show ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ), r∈Ioi (0:ℝ) from self_mem_nhdsWithin).mono fun r hr => (pour u h ht χ hχ hc ha (show r ≠ 0 from (show 0<r from hr).ne') i j b).symm
  unfold g score at hq; simp_rw [stillGreen] at hq; rw [hq]
  have hz' : (0:E4)∈U := ha (subset_tsupport χ (show 0∈support χ from fun hx => one_ne_zero (α:=ℝ) ((hz.eq_of_nhds.symm).trans hx)))
  have hd := h.cycle b i j 0 hz'
  have hp : u j b =ᶠ[𝓝 (0:E4)] -u b j := by filter_upwards [ht.mem_nhds hz'] with y hy; exact h.form _ _ _ hy
  rw [show grad i (u j b) 0 = -grad i (u b j) 0 from by rw [grad,GermD _ hp,D,fderiv_neg]; rfl] at hd
  linarith

end center
end YM.UVNext.FreeStress
