import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Topology.Baire.Lemmas

/-!
One-variable weak-boundary uniqueness. We only use it AFTER smearing horizontally;
strict values need not be bounded before smearing. The sequence of vertical boundary
values after smearing need only tend to a number (as in the Opens property). We use
Baire to bound intermediate strict values on some spatial interval (here the real part
of the complex coordinate). No continuation of a perturbative remainder to the
Lorentzian boundary is presumed.
-/

noncomputable section
namespace YM.Trace
open Function Filter MeasureTheory Complex Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option linter.unusedSectionVars false

def upper : Set ℂ := {z|0<z.im}
lemma upper_open : IsOpen upper := isOpen_lt continuous_const continuous_im
lemma upper_connected : IsPreconnected upper := by
  suffices h : Convex ℝ upper from h.isPreconnected
  intro x hx y hy a b ha hb hab; unfold upper at *
  simp only [mem_setOf_eq,Complex.real_smul, Complex.add_im,mul_im,ofReal_re,ofReal_im,zero_mul,add_zero] at *
  change a*x.im + b*y.im > 0; change 0<x.im at hx; change 0<y.im at hy
  rcases le_total a b with _|_ <;> nlinarith

def upperStrip (a b h : ℝ) := Ioo a b ×ℂ Ioo 0 h
def midStrip (a b h : ℝ) := Ioo a b ×ℂ Ioo (-h) h
lemma strips_open (a b h : ℝ) : IsOpen (upperStrip a b h) ∧ IsOpen (midStrip a b h) := by
  exact ⟨.inter (isOpen_Ioo.preimage continuous_re) (isOpen_Ioo.preimage continuous_im),
    .inter (isOpen_Ioo.preimage continuous_re) (isOpen_Ioo.preimage continuous_im)⟩
lemma pack_strip {a b h : ℝ} (hh:0<h) : upperStrip a b h ⊆ midStrip a b h := by
  intro x hx; obtain ⟨he,hp⟩ := mem_reProdIm.mp hx
  exact mem_reProdIm.mpr ⟨he,neg_lt.mpr (by have hpx : 0<x.im := hp.1; linarith),hp.2⟩ -- wrong

private lemma pack (x y : ℝ) (s t : Set ℝ) : (x+y*I) ∈ s ×ℂ t ↔ x∈s ∧ y∈t := by
  rw [mem_reProdIm]; simp

variable {a b h C x l y t : ℝ} {F : ℂ→ℂ}

omit C F in
private lemma mixed_rectangle (hx : x ∈ Ioo a b) (hu : l ∈ Ioo a b)
    (hy : y ∈ Ioo 0 h) (ht : t ∈ Ioo 0 h) : Rectangle (x+t*I) (l+y*I) ⊆ upperStrip a b h := by
  simp_rw [Rectangle,upperStrip]
  intro p hp; obtain ⟨hr,hi⟩ := mem_reProdIm.mp hp
  have h1 {a b u v s : ℝ} (h : s ∈ [[u,v]]) (hu : u∈ Ioo a b) (hv : v∈Ioo a b) : s∈Ioo a b := by
    simp only [mem_uIcc] at h
    obtain ⟨ha,hb⟩ := hu; obtain ⟨hc,hd⟩ := hv
    rcases h with ⟨h1,h2⟩|⟨h3,h4⟩ <;> exact ⟨by linarith, by linarith⟩
  exact mem_reProdIm.mpr ⟨h1 (by simpa using! hr) hx hu,h1 (by simpa using! hi) ht hy⟩

def liftFromZero (F : ℂ→ℂ) (w : ℂ) : ℂ := if 0 < w.im then
    I * ∫ v in (0:ℝ)..w.im, F (w.re + v*I) else 0

variable (HF : DifferentiableOn ℂ F (upperStrip a b h)) (hc : ∀ z ∈ upperStrip a b h, ‖F z‖ ≤ C)
    (Hlim : ∀ x ∈ Ioo a b, Tendsto (fun (y : ℝ) => F (x+y*I)) (𝓝[>] 0) (𝓝 0))
include HF
lemma hCuts (hx : x ∈ Ioo a b) (hu : l ∈ Ioo a b) (hy : y ∈ Ioo 0 h) (ht : t ∈ Ioo 0 h) :
    (∫ r in x..l, F (r + t*I)) + I * (∫ r in t..y, F (l+r*I)) =
      (∫ r in x..l, F (r + y*I)) + I * (∫ r in t..y, F (x+r*I)) := by
    have := HF.isConservativeOn _ _ (mixed_rectangle hx hu hy ht)
    simp only [wedgeIntegral,add_re, add_im,ofReal_im,ofReal_re, mul_I_re,mul_I_im,
      neg_zero,add_zero,zero_add,smul_eq_mul] at this
    rw [intervalIntegral.integral_symm x, intervalIntegral.integral_symm t] at this; linear_combination this

lemma horizontal_open_continuous (hy : y ∈ Ioo 0 h) :
    ContinuousOn (fun (x : ℝ) => F (x+y*I)) (Ioo a b) := by
    apply ContinuousOn.comp (g:=F) (f:=fun q : ℝ => (q:ℂ)+y*I) HF.continuousOn
    · fun_prop
    exact fun x hx => (pack ..).mpr ⟨hx,hy⟩

lemma vertical_open_continuous (hx : x ∈ Ioo a b) :
    ContinuousOn (fun (t : ℝ) => F (x+t*I)) (Ioo 0 h) := by
    apply ContinuousOn.comp (g:=F) (f:=fun q : ℝ => (x:ℂ)+q*I) HF.continuousOn
    · fun_prop
    exact fun y hy => (pack ..).mpr ⟨hx,hy⟩

include hc
lemma vertical_integrable (hx : x ∈ Ioo a b) (hy : y ∈ Ioo 0 h) :
    IntervalIntegrable (fun r : ℝ => F (x+r*I)) volume 0 y := by
  have hp : Ioc 0 y ⊆ Ioo 0 h := fun u hu => ⟨hu.1,hu.2.trans_lt hy.2⟩
  refine ⟨IntegrableOn.of_bound (Real.volume_Ioc (a:=0) (b:=y) ▸ ENNReal.ofReal_lt_top)
      (((vertical_open_continuous HF hx).mono hp).aestronglyMeasurable measurableSet_Ioc) C
      ((ae_restrict_mem measurableSet_Ioc).mono fun u hu => hc _ ((pack ..).mpr ⟨hx,hp hu⟩)),?_⟩
  rw [show Ioc y 0=∅ from Set.Ioc_eq_empty_of_le hy.1.le]; exact integrableOn_empty

lemma lift_at (x y : ℝ) (hy : 0<y) : liftFromZero F (x+y*I)=I*(∫ v in (0:ℝ)..y, F (x + v*I)) := by simp [liftFromZero,hy]
include hc
lemma lift_norm (hx : x ∈ Ioo a b) (hy : y ∈ Ioo 0 h) :
    ‖liftFromZero F (x+y*I)‖ ≤ max 0 C * |y| := by
  rw [liftFromZero]
  simp only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,if_pos hy.1,add_re,mul_I_re, neg_zero,add_zero,norm_mul,norm_I,one_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le_const (C:=max 0 C) ?_ |>.trans_eq (by rw [sub_zero])
  intro k hk
  rw [uIoc_of_le hy.1.le] at hk
  exact le_trans (hc _ ((pack ..).mpr ⟨hx,hk.1,hk.2.trans_lt hy.2⟩)) (le_max_right ..)

lemma vertical_tendsto (hh : 0 < h) (hx : x ∈ Ioo a b) : Tendsto (fun (t : ℝ) => liftFromZero F (x+t*I)) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have H : Tendsto (fun t : ℝ => max 0 C * |t|) (𝓝[>] 0) (𝓝 0) := by
     simpa only [abs_zero,mul_zero] using! (ContinuousAt.tendsto (show ContinuousAt (fun t : ℝ => max 0 C * |t|) 0 by fun_prop)).mono_left
        nhdsWithin_le_nhds
  have hE : Ioo 0 h ∈ 𝓝[>] (0:ℝ) := mem_nhdsWithin.mpr ⟨Iio h,isOpen_Iio,hh,fun _ hx => ⟨hx.2,hx.1⟩⟩
  exact squeeze_zero' (.of_forall fun _ => norm_nonneg _) (hft:= (show ∀ᶠ (t : ℝ) in 𝓝[>] 0, _ from hE).mono (fun r hr => lift_norm HF hc hx hr)) H

include Hlim
lemma horizontal_tendsto (hh : 0<h) (hx : x ∈ Ioo a b) (hu : l ∈ Ioo a b) :
    Tendsto (fun t : ℝ => ∫ r in x..l, F (r+t*I)) (𝓝[>] 0) (𝓝 0) := by
  have ht : Ι x l ⊆ Ioo a b := fun r hr => by
    simp only [mem_uIoc] at hr
    obtain ⟨ha,hb⟩ := hx; obtain ⟨hd,he⟩ := hu
    rcases hr with ⟨_,h2⟩|⟨h3,h4⟩ <;> exact ⟨by linarith, by linarith⟩
  have hE : Ioo 0 h ∈ 𝓝[>] (0:ℝ) := mem_nhdsWithin.mpr ⟨Iio h,isOpen_Iio,hh,fun _ hx => ⟨hx.2,hx.1⟩⟩
  rw [← intervalIntegral.integral_zero (E:=ℂ) (a:=x) (b:=l) (μ:=volume)]; apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => max 0 C) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hE] with t ht'
    exact ((horizontal_open_continuous HF ht').mono ht).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hE] with t ht'
    filter_upwards with r hr
    exact le_trans (hc _ ((pack ..).mpr ⟨ht hr,ht'⟩)) (le_max_right ..)
  exact ae_of_all _ fun r hr => Hlim _ (ht hr)

lemma lift_horizontal (hx : x ∈ Ioo a b) (hu : l ∈ Ioo a b) (hy : y ∈ Ioo 0 h) :
    liftFromZero F (l + y*I) - liftFromZero F (x+y*I) = ∫ r in x..l, F (r+y*I) := by
  have hh := hy.1.trans hy.2
  have hz := horizontal_tendsto HF hc Hlim hh hx hu |>.sub (vertical_tendsto HF hc hh hu) |>.add
    (vertical_tendsto HF hc hh hx)
  have he : ∀ᶠ (t:ℝ) in 𝓝[>] 0,
      (((∫ (r : ℝ) in x..l, F (r+t*I)) - liftFromZero F (l+t*I)) + liftFromZero F (x+t*I)) =
         (∫ r in x..l, F (r+y*I)) - (liftFromZero F (l+y*I)-liftFromZero F (x+y*I)) := by
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hh), self_mem_nhdsWithin] with t ht htp
    have htv : t ∈ Ioo 0 h := ⟨htp,ht⟩
    have hi x (hu' : x ∈ Ioo a b) := intervalIntegral.integral_add_adjacent_intervals
       (vertical_integrable HF hc (x:=x) hu' htv) ((vertical_integrable HF hc hu' htv).symm.trans (vertical_integrable HF hc hu' hy))
    have hs := hCuts HF hx hu hy htv
    rw [lift_at HF hc l y hy.1,lift_at HF hc x y hy.1,lift_at HF hc l t htv.1,lift_at HF hc x t htv.1]
    linear_combination hs - I*hi l hu + I*hi x hx
  simp only [sub_zero,add_zero] at hz
  have h0 := tendsto_nhds_unique hz (show Tendsto _ _ (𝓝 _) from tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))
  linear_combination h0

lemma lift_wedge {z w : ℂ} (hz : z ∈ upperStrip a b h) (hw : w∈upperStrip a b h) :
    liftFromZero F w - liftFromZero F z = wedgeIntegral z w F := by
    rcases mem_reProdIm.mp hz with ⟨hx,hy⟩; rcases mem_reProdIm.mp hw with ⟨hl,hk⟩
    have H := lift_horizontal HF hc Hlim hx hl hy
    simp only [re_add_im] at H
    rw [wedgeIntegral,smul_eq_mul,← H] -- then vertical term
    have hi :=(vertical_integrable HF hc hl hy).symm.trans (vertical_integrable HF hc hl hk)
    unfold liftFromZero; simp only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero,add_im,mul_I_im,
       zero_add,if_pos hy.1, if_pos hk.1]
    linear_combination -I * intervalIntegral.integral_add_adjacent_intervals (vertical_integrable HF hc hl hy) hi
lemma lift_deriv {z : ℂ} (hz : z ∈ upperStrip a b h) : HasDerivAt (liftFromZero F) (F z) z := by
  obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp ((strips_open a b h).1.mem_nhds hz)
  have hQ : liftFromZero F =ᶠ[𝓝 z] fun w=> wedgeIntegral z w F + liftFromZero F z :=
     Filter.Eventually.mono (Metric.ball_mem_nhds z hr) (fun w hw => eq_add_of_sub_eq (lift_wedge HF hc Hlim hz (hR hw)))
  have ht := (HF.mono hR).isConservativeOn.hasDerivAt_wedgeIntegral (HF.continuousOn.mono hR) (Metric.mem_ball_self hr)
  simpa using! (ht.add_const (liftFromZero F z)).congr_of_eventuallyEq hQ
lemma lift_diff : DifferentiableOn ℂ (liftFromZero F) (upperStrip a b h) := fun _ hz =>
    (lift_deriv HF hc Hlim hz).differentiableAt.differentiableWithinAt
lemma lift_continuous : ContinuousOn (liftFromZero F) (midStrip a b h) := by
  apply (strips_open ..).2.continuousOn_iff.mpr
  intro z hz
  obtain ⟨hx,hy⟩ := mem_reProdIm.mp hz
  by_cases hp : z.im > 0
  · exact (lift_deriv HF hc Hlim (mem_reProdIm.mpr ⟨hx,hp,hy.2⟩)).continuousAt
  by_cases hm : z.im < 0
  · apply (continuousAt_const (y:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [(continuous_im.tendsto z).eventually (gt_mem_nhds hm)] with w hw
    dsimp [liftFromZero]; rw [if_neg (show ¬ 0 < w.im from (show w.im<0 from hw).le.not_gt)]
  have hi : z.im=0 := (le_of_not_gt hp).antisymm (le_of_not_gt hm)
  have hv : liftFromZero F z=0 := by simp [liftFromZero,hi]
  have ht : Tendsto (fun w : ℂ => (max 0 C) * |w.im|) (𝓝 z) (𝓝 0) := by
     have := (continuousAt_const (y:=max 0 C)|>.mul continuous_im.continuousAt.abs).tendsto (x:=z)
     simpa only [Pi.mul_apply,hi, abs_zero,mul_zero] using! this
  have hbound : ∀ᶠ (w : ℂ) in 𝓝 z, ‖liftFromZero F w‖ ≤ max 0 C * |w.im| := Filter.Eventually.mono ((strips_open a b h).2.mem_nhds hz)
      (fun w hw => by
        obtain ⟨hx',hy'⟩ := mem_reProdIm.mp hw
        by_cases hy'' : w.im>0
        · have := lift_norm HF hc hx' ⟨hy'',hy'.2⟩; simpa only [re_add_im] using this
        simp only [liftFromZero,if_neg hy'',norm_zero]; positivity)
  unfold ContinuousAt; rw [hv]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (.of_forall fun _=>norm_nonneg _) hbound ht)

lemma wedge_mid {z w : ℂ} (hz : z ∈ midStrip a b h) (hw : w ∈ midStrip a b h) :
    liftFromZero (liftFromZero F) w - liftFromZero (liftFromZero F) z = wedgeIntegral z w (liftFromZero F) := by
  let K := liftFromZero F; change liftFromZero K w - liftFromZero K z = _
  obtain ⟨hx,hy⟩ := mem_reProdIm.mp hz; obtain ⟨hl,hy'⟩ := mem_reProdIm.mp hw
  have horizontal : liftFromZero K (w.re + z.im*I)-liftFromZero K z = ∫ r in z.re..w.re, K (r+z.im*I) := by
     by_cases ht : z.im > 0
     · have hK (p) (hp:p∈upperStrip a b h) : ‖K p‖ ≤ max 0 C * h := by
           obtain ⟨hr,hi⟩ := mem_reProdIm.mp hp
           refine le_trans (b:=max 0 C * |p.im|) (show _ from ?_) (mul_le_mul_of_nonneg_left (abs_le.mpr ?_) (le_max_left 0 C))
           · simpa only [re_add_im,K] using lift_norm HF hc hr hi
           exact ⟨neg_lt.mpr ((neg_lt_zero.mpr hi.1).trans (hi.1.trans hi.2)) |>.le,hi.2.le⟩
       have hk := lift_horizontal (lift_diff HF hc Hlim) hK (fun o ho => vertical_tendsto HF hc (ht.trans hy.2) (x:=o) ho) hx hl ⟨ht,hy.2⟩
       simpa only [re_add_im] using hk
     simp only [liftFromZero,add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,ht,if_false,sub_self (0:ℂ),K,intervalIntegral.integral_zero]
  rw [wedgeIntegral,smul_eq_mul,← horizontal]
  suffices ∀ y : ℝ, I * (∫ v in 0..y, K (w.re+v*I)) = liftFromZero K (w.re+y*I) from ?_
  · have hi (y : ℝ) (hy : y ∈ Ioo (-h) h) : IntervalIntegrable (fun v : ℝ => K (w.re+v*I)) volume 0 y := by
       apply ContinuousOn.intervalIntegrable
       refine (lift_continuous HF hc Hlim).comp (f:=fun v : ℝ=> (w.re : ℂ)+v*I) (by fun_prop)
          (fun x hu => (pack ..).mpr ⟨hl,?_⟩)
       rcases mem_uIcc.mp hu with he|he <;> obtain ⟨he1,he2⟩ := he
       all_goals change -h<x ∧ x<h; obtain ⟨hy1,hy2⟩ := hy; exact ⟨by linarith,by linarith⟩
    have hv := intervalIntegral.integral_add_adjacent_intervals (hi z.im hy)
        ((hi z.im hy).symm.trans (hi w.im hy'))
    have h1 := this w.im; rw [re_add_im] at h1
    have h2 := this z.im
    linear_combination -h1 + h2 - I * hv
  intro u
  by_cases hu : 0<u
  · simp [liftFromZero,hu]
  rw [liftFromZero]; simp only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,if_neg hu]
  -- integrand identically zero in interval
  rw [(by
     refine Eq.trans (intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) ?_) intervalIntegral.integral_zero
     intro z hz; change liftFromZero F _=0; rw [liftFromZero]; simp_rw [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add]
     rw [uIcc_comm,uIcc_of_le (le_of_not_gt hu)] at hz
     exact if_neg (show ¬ z>0 from hz.2.not_gt) : (∫ v in (0:ℝ)..u, K (w.re+(v:ℂ)*I)) = 0)]; ring

lemma lift_holo : DifferentiableOn ℂ (liftFromZero F) (midStrip a b h) := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn (U:=midStrip a b h) (strips_open ..).2).mp
  refine ⟨fun z w hw => ?_,lift_continuous HF hc Hlim⟩
  have h1 := hw (mem_reProdIm.mpr ⟨Set.left_mem_uIcc,Set.left_mem_uIcc⟩ : z∈Rectangle z w)
  have h2 := hw (mem_reProdIm.mpr ⟨Set.right_mem_uIcc,Set.right_mem_uIcc⟩ : w∈Rectangle z w)
  rw [← wedge_mid HF hc Hlim h1 h2,← wedge_mid HF hc Hlim h2 h1]; ring

lemma boundary_window (ha : a<b) (hh : 0<h) : EqOn F 0 (upperStrip a b h) := by
    let m := (((a+b)/2:ℝ):ℂ); let D := midStrip a b h
    have hm : m ∈ D := mem_reProdIm.mpr (by simp only [m, ofReal_re, ofReal_im,mem_Ioo]; exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩)
    obtain ⟨r, hr, hR⟩ := Metric.mem_nhds_iff.mp ((strips_open a b h).2.mem_nhds hm)
    have hI : m-(r/2:ℝ)*I ∈ Metric.ball m r := Metric.mem_ball.mpr (by simp [abs_of_pos,hr])
    have hB : liftFromZero F =ᶠ[𝓝 (m-(r/2:ℝ)*I)] 0 := by
       filter_upwards [(continuous_im.tendsto _).eventually (gt_mem_nhds (by simp [m,hr] : (m-(r/2:ℝ)*I).im<0))]
         with w (hw : w.im < 0)
       rw [liftFromZero,if_neg (by linarith)]; rfl
    have he := ((lift_holo HF hc Hlim).mono hR).analyticOnNhd Metric.isOpen_ball
      |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const (convex_ball .. |>.isPreconnected) hI hB
    have hI' : (m+(r/2:ℝ)*I) ∈ Metric.ball m r := Metric.mem_ball.mpr (by simp [hr,abs_of_pos])
    have hi' : (m+ (r/2:ℝ)*I).im ∈ Ioi (0:ℝ) := by simp [m,hr]
    have hv : (m+(r/2:ℝ)*I) ∈ upperStrip a b h := mem_reProdIm.mpr ⟨(mem_reProdIm.mp (hR hI')).1,
       hi', (mem_reProdIm.mp (hR hI')).2.2⟩
    have H : F =ᶠ[𝓝 (m+(r/2:ℝ)*I)] 0 := by
       filter_upwards [Metric.isOpen_ball.mem_nhds hI',(strips_open ..).1.mem_nhds hv] with w hw hg
       have hy : liftFromZero F =ᶠ[𝓝 w] fun _ => 0 := (he.mono ?_).eventuallyEq.filter_mono (Filter.le_principal_iff.mpr (Metric.isOpen_ball.mem_nhds hw))
       · have ht := (hy.hasDerivAt_iff).mpr (hasDerivAt_const w 0)
         exact (lift_deriv HF hc Hlim hg).unique ht
       exact Subset.rfl
    have Hc : IsPreconnected (upperStrip a b h) := (Convex.inter ((convex_Ioo a b).linear_preimage Complex.reCLM.toLinearMap)
       ((convex_Ioo 0 h).linear_preimage Complex.imCLM.toLinearMap)).isPreconnected
    exact HF.analyticOnNhd (strips_open ..).1 |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const Hc hv H
omit HF hc Hlim
/-- Uniqueness when the holomorphic function has tested horizontal slices with zero limit -
proof on the resulting scalar function. Only asks pointwise (not uniform tempered order). -/
theorem vanishes_of_vertical_limit (h : DifferentiableOn ℂ F upper)
    (e : ∀ x : ℝ, Tendsto (fun (y:ℝ) => F (x + y*I)) (𝓝[>] 0) (𝓝 0)) : EqOn F 0 upper := by
  let k (n : ℕ) := ((n:ℝ)+1)⁻¹
  let D (n) := {x : ℝ | ∀ y∈Ioo 0 (k n), ‖F (x + y*I)‖ ≤ n}
  have he (n : ℕ) : IsClosed (D n) := by
     simp only [D,setOf_forall]
     refine isClosed_iInter fun y => isClosed_iInter fun hy => isClosed_le ?_ continuous_const
     have ht : ∀ x ∈ upper, ContinuousAt F x := upper_open.continuousOn_iff.mp h.continuousOn
     exact continuous_iff_continuousAt.mpr (fun x=> ((ht _ (by unfold upper; simpa using hy.1)).comp (by fun_prop)).norm)
  have hd : ⋃ n, D n=univ := iUnion_eq_univ_iff.mpr fun x => by
     obtain ⟨δ,hδ,hx⟩ := (Metric.tendsto_nhdsWithin_nhds (a:=0) (b:=0)).mp (e x) 1 one_pos
     have hh : Tendsto k atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1
       (tendsto_natCast_atTop_atTop (R:=ℝ)))
     obtain ⟨n,hk,hn⟩ := ((hh.eventually (gt_mem_nhds hδ)).and (eventually_ge_atTop 1)).exists
     refine ⟨n,fun y hy => le_trans (show _≤1 from ?_) (mod_cast hn)⟩
     have h := abs_of_pos hy.1
     simpa [dist_eq,h] using (hx hy.1 (by simpa [Real.dist_eq,abs_of_pos hy.1] using hy.2.trans hk)).le
  obtain ⟨n,x,hx⟩ := nonempty_interior_of_iUnion_of_closed he hd
  obtain ⟨s,hs,hS⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  have hp := boundary_window (F:=F) (a:=x-s) (b:=x+s) (h:=k n)
      (h.mono (fun z hz => (mem_reProdIm.mp hz).2.1)) (C:=(n:ℝ)) (fun z hz => by
        obtain ⟨⟨hv,hv'⟩,hy⟩:=mem_reProdIm.mp hz
        have ht : z.re∈D n := interior_subset (hS (Metric.mem_ball.mpr (by rw [Real.dist_eq]; exact abs_lt.mpr (by constructor <;> linarith))))
        simpa only [re_add_im] using! ht z.im hy)
      (fun u _ => e u) (show x-s<x+s by linarith) (by dsimp only [k]; positivity)
  let z := (x:ℂ)+(k n/2:ℝ)*I
  have hk : 0<k n := by dsimp only [k]; positivity
  have hz : z∈upperStrip (x-s) (x+s) (k n) := (pack ..).mpr ⟨⟨by linarith,by linarith⟩,⟨by positivity,by linarith⟩⟩
  have hz' : z∈upper := (mem_reProdIm.mp hz).2.1
  exact h.analyticOnNhd upper_open |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const upper_connected hz'
    (hp.eventuallyEq.filter_mono (le_principal_iff.mpr ((strips_open ..).1.mem_nhds hz)))
end YM.Trace
