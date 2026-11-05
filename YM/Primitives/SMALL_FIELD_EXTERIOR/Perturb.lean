import YM.Primitives.SMALL_FIELD_EXTERIOR.Normal
import YM.Work.A15


/-!
# Real normalized expectations in a varying potential

Use a fixed domain; hypotheses cover a genuine parameter neighborhood jointly
and do not require differentiable data in y to get just the identity. This
is differentiation of the same normalized law, not of branch, period or
history choices used to construct inputs for different queries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

variable {ι : Type} [Fintype ι] {V V' F F' : ℝ → Points ι → ℝ}
    {r x m d : ℝ} {I : Set ℝ} {f g H : Points ι → ℝ}

/-- Real parameter (no changing domains). Put `V'` in with its sign as
a potential, hence the minus in the response. -/
structure Change (r : ℝ) (I : Set ℝ) (F F' : ℝ → Points ι → ℝ) : Prop where
  total : ContinuousOn (Function.uncurry F) (I ×ˢ cube ι r)
  slope : ContinuousOn (Function.uncurry F') (I ×ˢ cube ι r)
  has (x : ℝ) : x∈I → ∀ y∈cube ι r, HasDerivAt (fun z => F z y) (F' x y) x

lemma Change.fixed (hf : ContinuousOn f (cube ι r)) : Change r I (fun _ => f) 0 :=
  ⟨hf.comp continuous_snd.continuousOn (fun _ hx => hx.2),continuousOn_const,fun x _ y _ => hasDerivAt_const x (f y)⟩
lemma Change.density (h : Change r I V V') (hf : Change r I F F') : Change r I
    (fun x y => Real.exp (-V x y) * F x y) (fun x y => Real.exp (-V x y) * (F' x y-V' x y * F x y)) := by
  refine ⟨(Real.continuous_exp.comp_continuousOn h.total.neg).mul hf.total, (Real.continuous_exp.comp_continuousOn h.total.neg).mul
    (hf.slope.sub (h.slope.mul hf.total)),fun x hx y hy => ?_⟩
  convert! ((h.has x hx y hy).neg.exp).mul (hf.has x hx y hy) using 1; simp only [Pi.neg_apply]; ring
lemma held_cont (h : ContinuousOn (uncurry V) (I ×ˢ cube ι r)) {t} (ht : t∈I) : ContinuousOn (V t) (cube ι r) :=
  h.comp (f:=fun u : Points ι => (t,u))
    (continuousOn_const.prodMk continuousOn_id) (fun _ hi => ⟨ht,hi⟩)
lemma Change.carry (h : Change r I F F') (hi : IsCompact I) (hx : I ∈ 𝓝 x) :
    HasDerivAt (fun t => ∫ y in cube ι r, F t y) (∫ y in cube ι r,F' x y) x := by
  let μ := (volume : Measure (Points ι)).restrict (cube ι r)
  have he : x∈I := mem_of_mem_nhds hx
  have ht t (ht : t∈I) : Integrable (F t) μ := (held_cont h.total ht).integrableOn_compact (cube_compact r)
  obtain ⟨K,hK⟩ := (hi.prod (cube_compact (ι:=ι) r)).exists_bound_of_continuousOn h.slope
  have hm := ae_restrict_mem (μ:=(volume:Measure (Points ι))) (cube_meas r)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hx
    ((show ∀ᶠ t in 𝓝 x, t∈I from hx).mono fun t ht' => (ht t ht').1) (ht _ he)
    (show AEStronglyMeasurable (F' x) μ from ((held_cont h.slope he).integrableOn_compact (cube_compact r)).1)
    (hm.mono fun y hy t ht => hK (t,y) ⟨ht,hy⟩) (show Integrable (fun _ => K) μ from continuousOn_const.integrableOn_compact (cube_compact r))
    (hm.mono fun y hy t ht => h.has t ht y hy)).2
lemma Change.price (h : Change r I V V') (hf : Change r I F F') (hi : IsCompact I) (hx : I∈𝓝 x) :
    HasDerivAt (fun t => raw r (V t) (F t)) (raw r (V x) (F' x)-raw r (V x) (V' x * F x)) x := by
  have ht : x∈I := mem_of_mem_nhds hx
  rw [← raw_sub (held_cont h.total ht) (held_cont hf.slope ht) ((held_cont h.slope ht).mul (held_cont hf.total ht))]
  exact (h.density hf).carry hi hx
lemma Change.response (h : Change r I V V') (hf : Change r I F F') (hr : 0<r) (hi : IsCompact I) (hx : I∈𝓝 x) :
    HasDerivAt (fun t => mean r (V t) (F t)) (mean r (V x) (F' x)-covariance r (V x) (V' x) (F x)) x := by
  have he : 0 < raw r (V x) 1 := raw_one_pos hr (held_cont h.total (mem_of_mem_nhds hx))
  have hz : HasDerivAt (fun t => raw r (V t) 1) (-raw r (V x) (V' x)) x := by
    convert! h.price (F:=fun _ => 1) (F':=0) (Change.fixed continuousOn_const) hi hx using 1; simp [raw]
  convert! (h.price hf hi hx).div hz he.ne' using 1
  unfold covariance mean; field_simp; ring

lemma mark_change (hH : ContinuousOn H (cube ι r)) (hf : ContinuousOn f (cube ι r)) :
    Change r I (fun t => H-t • f) (fun _ => -f) := by
  have hp := (Change.fixed (I:=I) hH).total
  have hh := (Change.fixed (I:=I) hf).total
  refine ⟨hp.sub (continuous_fst.continuousOn.smul hh),hh.neg,fun x _ y _ => ?_⟩
  convert! (hasDerivAt_const x (H y)).sub ((hasDerivAt_id' x).mul_const (f y)) using 1; simp
lemma source (hH : ContinuousOn H (cube ι r)) (hf : ContinuousOn f (cube ι r)) (hg : ContinuousOn g (cube ι r)) (hr : 0<r) (x : ℝ) :
    let W : ℝ → Points ι → ℝ := fun t => H-t • f
    HasDerivAt (fun t => mean r (W t) g) (covariance r (W x) f g) x := by
  intro W
  convert! ((mark_change hH hf).response (x:=x) (Change.fixed hg) hr (isCompact_Icc (a:=x-1) (b:=x+1)) (Icc_mem_nhds (by linarith) (by linarith))) using 1
  unfold covariance mean
  rw [neg_mul]
  simp only [raw,W,Pi.zero_apply,Pi.neg_apply,mul_zero,mul_neg,integral_zero, integral_neg]; ring
end YM.Primitives.SmallFieldExterior
