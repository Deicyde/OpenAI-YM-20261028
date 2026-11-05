import YM.Work.C14
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! Some tools for the positive-sign Wightman testing convention. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace
open Boundary Function Filter MeasureTheory Set Complex
open scoped ContDiff Topology BigOperators
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def plus : Probe V →L[ℂ] Probe V := (Probe.pref V : ℂ) • Probe.port

lemma plus_eq (f : Probe V) (p : V) : plus f p = ∫ x, Probe.plane x p * f x := by
  change (Probe.pref V : ℂ) * Probe.port f p = _
  rw [Probe.port_eq]
  rw [Complex.real_smul, Complex.ofReal_inv]
  have H : (↑(Probe.pref V) : ℂ) ≠ 0 := by exact_mod_cast Probe.prepos.ne'
  field_simp

lemma plus_eq_hat (f : Probe V) (p : V) : plus f p=Probe.hat f (-p) := by
  simp only [plus_eq,Probe.hat_eq,neg_neg]

lemma plus_bar (f : Probe V) (p : V) : plus (Probe.bar f) p = star (plus f (-p)) := by
  rw [plus_eq,plus_eq, Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with u
  rw [Probe.bar_at,show Probe.plane u p = star (Probe.plane u (-p)) by
      simpa using Probe.plane_inverse u (-p)]
  exact (map_mul (starRingEnd ℂ) (Probe.plane u (-p)) (f u)).symm

abbrev CC (f : Probe V) := HasCompactSupport (⇑f)

def conv (a b : Probe V) : Probe V := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) a b

lemma conv_eq (a b : Probe V) (k : V) : conv a b k = ∫ x, a x * b (k-x) :=
  (SchwartzMap.convolution_apply ..).trans (convolution_def (ContinuousLinearMap.mul ℂ ℂ))

lemma conv_eqFun (a b : Probe V) : ⇑(conv a b) = convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume :=
  funext fun k => (conv_eq a b k).trans (convolution_def (ContinuousLinearMap.mul ℂ ℂ)).symm

lemma conv_comm (a b : Probe V) : conv a b = conv b a := by
  have H : (ContinuousLinearMap.mul ℂ ℂ).flip = ContinuousLinearMap.mul ℂ ℂ := by
    refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_; exact mul_comm y x
  apply DFunLike.coe_injective
  rw [conv_eqFun, conv_eqFun, ← convolution_flip (ContinuousLinearMap.mul ℂ ℂ), H]

lemma conv_CC {a b : Probe V} (ha : CC a) (hb : CC b) : CC (conv a b) :=
by
  unfold CC; rw [conv_eqFun]; exact ha.convolution (ContinuousLinearMap.mul ℂ ℂ) hb

lemma func_integral (w : Distn V) (a b : Probe V) (ha : CC a) :
    w (conv a b) = ∫ x, a x * w (Probe.ahead x b) := by
  let K := tsupport a
  have hm : MeasurableSet K := ha.measurableSet
  let μ : Measure K := (volume : Measure V).comap ((↑) : K→V)
  let t (x : V) := a x • Probe.ahead x b
  have ht : Continuous t := a.continuous.smul (Work.C14.ahead_cont b)
  have ht0 (x : V) (hx : x ∉ K) : t x = 0 := by
    rw [show t x = a x • _ from rfl, image_eq_zero_of_notMem_tsupport hx, zero_smul]
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp ha
  haveI : IsFiniteMeasure μ := by
    constructor
    rw [(MeasurableEmbedding.subtype_coe hm).comap_apply, image_univ, Subtype.range_coe]
    exact ha.measure_lt_top
  have hsub (f : V → ℂ) (hf : ∀ x, x ∉ K → f x=0) : (∫ x : K, f x ∂μ) = ∫ x, f x :=
    (integral_subtype_comap hm f).trans (setIntegral_eq_integral_of_forall_compl_eq_zero hf)
  have he (p) : conv a b p = ∫ x : K,t x p∂μ := (conv_eq a b p).trans
    ((hsub (fun x => t x p) (fun x hx => by rw [ht0 x hx]; rfl)).symm)
  rw [Spark.allowance μ (t ∘ ((↑) : K→V)) (conv a b) he (ht.comp continuous_subtype_val) w, Function.comp_def]
  rw [hsub (fun x => w (t x)) (fun x hx => by rw [ht0 x hx,map_zero])]
  simp only [t,map_smul,smul_eq_mul]

lemma wave_integral_test {H : Hilbert} (v : Probe V →L[ℂ] H) (a b : Probe V) (ha : CC a) :
    v (conv a b) = ∫ x, a x • v (Probe.ahead x b) := by
  have hi : Integrable (fun x => a x • v (Probe.ahead x b)) :=
    (a.continuous.smul (v.continuous.comp (Work.C14.ahead_cont b))).integrable_of_hasCompactSupport
      (ha.smul_right)
  suffices ∀ p : H, inner ℂ p (v (conv a b)) = inner ℂ p (∫ x, a x • v (Probe.ahead x b)) by
    exact ext_inner_left ℂ this
  intro p
  rw [← innerSL_apply_apply,← innerSL_apply_apply, ← (innerSL ℂ p).integral_comp_comm hi]
  simpa only [ContinuousLinearMap.comp_apply, map_smul,smul_eq_mul] using
    func_integral ((innerSL ℂ p).comp v) a b ha

/-- Unnormalized rescaling within Schwartz at an arbitrary nonzero real factor. -/
noncomputable def adjusted (f : Probe V) (c : ℝ) : Probe V :=
  if h : c=0 then f else Probe.along (ContinuousLinearEquiv.smulLeft (Units.mk0 c h)) f

lemma adjusted_eq (f : Probe V) {c : ℝ} (h : c ≠ 0) (x : V) : adjusted f c x = f (c • x) := by
  rw [adjusted,dif_neg h]; rfl

lemma adjusted_CC {f : Probe V} (hf : CC f) (c : ℝ) : CC (adjusted f c) := by
  by_cases h : c=0
  · rw [adjusted,dif_pos h]; exact hf
  have H := hf.comp_homeomorph
    (ContinuousLinearEquiv.smulLeft (M₁:=V) (R₁:=ℝ) (Units.mk0 c h)).toHomeomorph
  rwa [show ((⇑f) ∘ _) = ⇑(adjusted f c) from funext (by intro x; exact (adjusted_eq f h x).symm)] at H

def cut (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [HasContDiffBump V] : ContDiffBump (0:V) := ⟨1,2,by norm_num,by norm_num⟩

def ruler (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] : Probe V :=
  let t := cut V
  (t.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp t.contDiff)

lemma ruler_CC : CC (ruler V) := by
  change HasCompactSupport (Complex.ofReal ∘ fun y => cut V y)
  exact (cut V).hasCompactSupport.comp_left Complex.ofReal_zero

lemma ruler_one {x : V} (hx : ‖x‖ ≤ 1) : ruler V x=1 := by
  change ((cut V x):ℂ)=_
  rw [(cut V).one_of_mem_closedBall]
  · simp
  simpa [cut] using hx

def cutTest (f : Probe V) (r : ℝ) : Probe V := Probe.sew f (adjusted (ruler V) r⁻¹)
lemma cutTest_eq (f : Probe V) {r : ℝ} (hr : r ≠ 0) (x : V) :
    cutTest f r x = f x * ruler V (r⁻¹ • x) := by rw [cutTest,Probe.sews,adjusted_eq _ (inv_ne_zero hr)]
lemma cutTest_CC (f : Probe V) (r : ℝ) : CC (cutTest f r) := by
  unfold CC; rw [show ⇑(cutTest f r)=⇑f * ⇑(adjusted (ruler V) r⁻¹) from funext (fun x => Probe.sews _ _ x)]; exact (adjusted_CC ruler_CC r⁻¹).mul_left
    -- function coercion changed, CC might not reduce

theorem cutTest_limit (f : Probe V) : Tendsto (cutTest f) atTop (𝓝 f) := by
  rw [Probe.tendN]
  intro m n ε hε
  let k := ruler V; let G (r : ℝ) := (fun y : V => k (r⁻¹ • y)) - (fun _ => (1 : ℂ))
  have hg (r : ℝ) : ContDiff ℝ ∞ (G r) := by unfold G; exact ((k.smooth ⊤).comp (show ContDiff ℝ ∞ _ from contDiff_const.smul contDiff_id)).sub contDiff_const
  let z (j) := Probe.size 0 j k+1
  have hg' (r : ℝ) (hr : 1 ≤ r) x j : ‖iteratedFDeriv ℝ j (G r) x‖ ≤ z j := by
    rw [show G r = (fun y : V => k (r⁻¹ • y))-(fun _ => (1:ℂ)) from rfl,
      iteratedFDeriv_sub_apply (by exact ((k.smooth j).comp (contDiff_const.smul contDiff_id)).contDiffAt)
        (by exact contDiffAt_const), iteratedFDeriv_comp_const_smul _ (k.smooth j)]
    let v := iteratedFDeriv ℝ j k (r⁻¹ • x)
    have h : ‖(r⁻¹)^j • v‖ ≤ Probe.size 0 j k := by
      rw [norm_smul,Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hr))).trans
        (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ k j _)
    refine (norm_sub_le _ _).trans (add_le_add h ?_)
    rcases j with _ | i; · simp
    simp [iteratedFDeriv_succ_const]
  let D := ∑ i ∈ Finset.range (n+1),((n.choose i:ℕ):ℝ) * Probe.size (m+1) i f * z (n-i)
  have hz i : 0≤z i := by dsimp only [z,Probe.size]; positivity
  have hd : 0≤D := Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (apply_nonneg ..)) (hz _))
  have hlim : Tendsto (fun t : ℝ => D/t) atTop (𝓝 0) := by
    simpa using! (tendsto_const_nhds (f:=atTop) (x:=D)).div_atTop tendsto_id
  filter_upwards [eventually_ge_atTop (1:ℝ), hlim.eventually (gt_mem_nhds hε)] with r hr hsmall
  apply lt_of_le_of_lt _ hsmall
  have hr' : 0<r := zero_lt_one.trans_le hr
  rw [Probe.size]
  have heq : ⇑(cutTest f r - f)=⇑f * G r := by ext x; simp [G,k,cutTest_eq f hr'.ne',mul_sub]
  refine SchwartzMap.seminorm_le_bound ℂ m n _ (by positivity) ?_
  intro x
  by_cases hx : r ≤ ‖x‖
  · rw [heq,le_div_iff₀ hr',mul_right_comm]
    apply le_trans (b := ‖x‖^(m+1)*‖iteratedFDeriv ℝ n (⇑f * G r) x‖)
    · rw [pow_succ]; gcongr
    refine le_trans (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (f.smooth ⊤) (hg r) x
      (show ↑n ≤ (∞:ℕ∞ω) by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))) (by positivity)) ?_
    rw [Finset.mul_sum]; unfold D
    apply Finset.sum_le_sum; intro i hi
    grw [show ‖x‖^(m+1)*(_*‖iteratedFDeriv ℝ i (⇑f) x‖ * _)=
        ((n.choose i:ℕ):ℝ) * (‖x‖^(m+1)*‖iteratedFDeriv ℝ i (⇑f) x‖)*‖iteratedFDeriv ℝ (n-i) (G r) x‖ by ring,
      SchwartzMap.le_seminorm ℂ (m+1) i f x, hg' r hr x (n-i)]
  have hb := lt_of_not_ge hx
  have he : ⇑(cutTest f r - f) =ᶠ[𝓝 x] 0 := by
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hb)] with y hy
    change cutTest f r y - f y=0
    rw [cutTest_eq _ hr'.ne', ruler_one, mul_one, sub_self]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left (show ‖y‖<r from hy).le (by positivity)
         _ = 1 := inv_mul_cancel₀ hr'.ne'
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_zero,Pi.zero_apply, norm_zero, mul_zero]
  change 0 ≤ D/r
  positivity

def normalized (f : Probe V) (r : ℝ) : Probe V := (r^Module.finrank ℝ V) • adjusted f r
lemma normalized_eq (f : Probe V) {r : ℝ} (hr : 0<r) (x : V) :
    normalized f r x = (r^Module.finrank ℝ V) • f (r • x) := by
  change (r^Module.finrank ℝ V) • adjusted f r x = _; rw [adjusted_eq _ hr.ne']
lemma normalized_CC {f : Probe V} (hf : CC f) (r : ℝ) : CC (normalized f r) :=
  HasCompactSupport.smul_left (f:=Function.const _ (r^Module.finrank ℝ V)) (adjusted_CC hf r)

lemma plus_normalized (f : Probe V) {r : ℝ} (hr : 0<r) (p : V) :
    plus (normalized f r) p = plus f (r⁻¹ • p) := by
  simp_rw [plus_eq, normalized_eq f hr, mul_smul_comm]
  rw [MeasureTheory.integral_smul]
  have heQ (x : V) : Probe.plane (r•x) (r⁻¹ • p) = Probe.plane x p := by
    simp [Probe.plane, inner_smul_left,inner_smul_right,hr.ne']
  have hh : (∫ x : V, Probe.plane ((r:ℝ) • x) (r⁻¹ • p) * f (r • x)) = _ :=
     MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
       (fun x : V => Probe.plane x (r⁻¹ • p) * f x) _ (hR:=hr.le)
  simp_rw [heQ] at hh; rw [hh, smul_smul, mul_inv_cancel₀ (pow_pos hr _).ne',one_smul]

lemma adjusted_size (f : Probe V) {r : ℝ} (hr : 1 ≤ r) (a b : ℕ) :
    Probe.size a b (adjusted f r) ≤ r^b * Probe.size a b f := by
  have hr' := zero_lt_one.trans_le hr
  unfold Probe.size
  refine SchwartzMap.seminorm_le_bound ℂ _ _ _ (mul_nonneg (pow_nonneg hr'.le _) (apply_nonneg ..)) fun x => ?_
  rw [show (adjusted f r : V→ℂ)=(fun x : V => f (r • x)) from funext (adjusted_eq f hr'.ne'),
    iteratedFDeriv_comp_const_smul r (f.smooth b), norm_smul, Real.norm_of_nonneg (pow_nonneg hr'.le _),mul_left_comm]
  gcongr
  refine le_trans ?_ (SchwartzMap.le_seminorm ℂ a b f (r • x))
  gcongr; simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hr'] using le_mul_of_one_le_left (norm_nonneg x) hr

set_option maxHeartbeats 1000000
lemma normalized_cost {J : Type*} [NormedAddCommGroup J] [NormedSpace ℂ J] (v : Probe V →L[ℂ] J) (f : Probe V) :
    ∃ (n : ℕ) (A : ℝ), 0≤A ∧ ∀ r : ℝ, 1 ≤ r → ‖v (normalized f r)‖ ≤ A*r^n := by
  obtain ⟨k,c,-,hc⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ J).comp v.toLinearMap) (continuous_norm.comp v.continuous)
  let n := k.sup Prod.snd; let D := Module.finrank ℝ V
  let B := ∑ i∈k, Probe.size i.1 i.2 f
  have hb : 0≤B := Finset.sum_nonneg (fun _ _ => apply_nonneg ..)
  refine ⟨D+n, c*B,mul_nonneg c.coe_nonneg hb,fun r hr => (hc (normalized f r)).trans ?_⟩
  suffices hp : k.sup (schwartzSeminormFamily ℂ _ _) (normalized f r) ≤ (r^(D+n))*B by
     change (c:ℝ) * ((Finset.sup k (schwartzSeminormFamily ℂ _ _)) _) ≤ _; exact (mul_le_mul_of_nonneg_left hp c.coe_nonneg).trans_eq (by ring)
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro i hi; change SchwartzMap.seminorm ℂ i.1 i.2 _ ≤ _
  rw [normalized,← Complex.coe_smul, map_smul_eq_mul, norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),pow_add,mul_assoc]
  gcongr
  have hi' : i.2 ≤ n := Finset.le_sup hi
  exact (adjusted_size f hr i.1 i.2).trans (mul_le_mul (pow_le_pow_right₀ hr hi')
    (Finset.single_le_sum (f:=fun p=>Probe.size p.1 p.2 f) (fun _ _ => apply_nonneg ..) hi) (apply_nonneg ..) (by positivity))

set_option maxHeartbeats 1000000
def initial (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] : Probe V :=
  let k := cut V
  ((k.hasCompactSupport_normed (μ:=volume)).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp k.contDiff_normed)

lemma initial_CC : CC (initial V) :=
  ((cut V).hasCompactSupport_normed (μ:=volume)).comp_left Complex.ofReal_zero

lemma plus_initial : plus (initial V) (0:V)=1 := by
  simp only [plus_eq,Probe.plane_zero,one_mul]
  change (∫ x : V, ofRealCLM ((cut V).normed volume x))=_
  rw [ofRealCLM.integral_comp_comm ((cut V).integrable_normed (μ:=volume)),
    (cut V).integral_normed]; simp

theorem plus_fits : ∃ f : ℕ→Probe V, (∀ i,CC (f i)) ∧ ∀ x,∃ i, plus (f i) x ≠ 0 := by
  let I := {f : Probe V // CC f}
  letI : Nonempty I := by exact ⟨initial V,initial_CC⟩
  let U (f : I) := {x|plus f.val x ≠ 0}
  have hU : univ ⊆ ⋃ i, U i := by
    intro x _
    have hh : Tendsto (fun r : ℝ => plus (initial V) (r⁻¹ • x)) atTop (𝓝 (plus (initial V) 0)) :=
      (plus (initial V)).continuous.continuousAt.tendsto.comp (by simpa using (tendsto_inv_atTop_zero (𝕜:=ℝ)).smul_const x)
    obtain ⟨r,hr,ht⟩ := ((eventually_ge_atTop (1:ℝ)).and (hh.eventually (isOpen_ne.mem_nhds
      (show plus (initial V) 0 ≠ 0 from (plus_initial (V:=V)) ▸ one_ne_zero)))).exists
    exact mem_iUnion.mpr ⟨⟨normalized (initial V) r,normalized_CC initial_CC _⟩,
        by change plus (normalized (initial V) r) x ≠ 0; rwa [plus_normalized _ (zero_lt_one.trans_le hr)]⟩

  obtain ⟨k,hk⟩ := isLindelof_univ.indexed_countable_subcover U
    (fun f => (plus f.val).continuous.isOpen_support) hU
  exact ⟨fun i => k i, fun i => (k i).property, fun x => mem_iUnion.mp (hk (mem_univ x))⟩

end YM.Trace
