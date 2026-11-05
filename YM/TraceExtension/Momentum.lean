import YM.TraceExtension.Relative

/-!
# Identification of the measure in the vacuum theory

Use product tests to identify the spectral PVM masses of states in the actual field Hilbert
space, not presuming the cone result for an auxiliary, fixed-axis OS chamber. Scalar
covariance transport for a group element follows by the same identification. -/

set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral OS
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace

lemma volume2 : MeasurePreserving (fun p : Points 2 => (p 0,p 1)) volume volume :=
    (volume_preserving_finTwoArrow E4).comp (Points.volume_product 2)
lemma embedding2 : MeasurableEmbedding (fun p : Points 2 => (p 0,p 1)) := by
    let M := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E4)).toHomeomorph.toMeasurableEquiv).trans MeasurableEquiv.finTwoArrow
    exact M.measurableEmbedding

def productTest (f g : Probe E4) := Joint.materialize 2 ![Probe.bar f,g]
lemma productTest_apply (f g : Probe E4) (x : Points 2) : productTest f g x=star (f (x 0))*g (x 1) := by
    simp [productTest,Fin.prod_univ_two]

lemma waveTest_product (f g : Probe E4) (p : E4) : waveTest (productTest f g) p =
    star (testPlus f p) * testPlus g p := by
  rw [waveTest_apply,testPlus_apply,testPlus_apply,Complex.star_def,← integral_conj,← integral_prod_mul]
  let K := fun a : E4 × E4 => star (Probe.plane a.1 p * f a.1) * (Probe.plane a.2 p * g a.2)
  have hp := volume2.integral_comp embedding2 K
  refine Eq.trans ?_ hp
  apply integral_congr_ae; filter_upwards with x
  have he : Probe.plane p (x 1-x 0) = Probe.plane (x 1) p * star (Probe.plane (x 0) p) := by
    rw [sub_eq_add_neg,Probe.plane_add,Probe.plane_inverse,Probe.plane_dot (x 1), Probe.plane_dot (x 0)]
  dsimp only [K]; rw [productTest_apply,he,star_mul]; ring

variable {G : Gauge} {L : Register G} {S T : Table L} {C : Chamber T timeAxis}
  {F : Waves S} {B : Small S C} {W : Surface S} {R : Wightman S} {X : Table.Rotation S} {rs : S.RealSpin}

/-- Smearing (complex linear). -/
def excitation (D : Fields S) (v : S.Union) (f : Probe E4) : D.H := D.vector [(v,f)]

lemma norm_read (h : Bid.Hull B F R.J) (hm : F.Breathes) (he : F.Opens W)
    (hr : R.Realizes (W:=W) X rs) (v : S.Union) (f g : Probe E4) :
    inner ℂ (excitation R.operators v f) (excitation R.operators v g) =
      ∫ p, star (testPlus f p)*testPlus g p ∂spectralMeasure B v := by
    unfold excitation; rw [Fields.general _ _ hr.meets _ hr.adj]
    have hx : W.kernel R.J [(v,f)] [(v,g)] = W.W 2 (pairV R.J v) (productTest f g) := by
      change W.W 2 _ (Joint.materialize 2 _) = W.W 2 _ (Joint.materialize 2 _)
      congr 2
      · funext i; fin_cases i <;> rfl

    rw [hx,surface_integral h hm he]; simp_rw [waveTest_product]

def probeWeight (f : Probe E4) (x : E4) : ℝ≥0 := ‖testPlus f x‖₊ ^ 2
lemma probe_cont (f : Probe E4) : Continuous (probeWeight f) := by unfold probeWeight; fun_prop
lemma probe_meas (f : Probe E4) : Measurable (fun p => (probeWeight f p : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (probe_cont f).measurable

lemma test_trans (f : Probe E4) (b p : E4) : testPlus (Joint.push (Poincare.translation b) f) p =
    Probe.plane p b * testPlus f p := by
    rw [testPlus_apply,testPlus_apply,← integral_const_mul, ← integral_add_left_eq_self _ b]
    refine integral_congr_ae (ae_of_all _ fun x => ?_); dsimp only
    rw [Probe.plane_dot (b+x), Probe.plane_add, Probe.plane_dot p x, Joint.push_at]
    simp [Poincare.backwards,Poincare.translation,mul_assoc]

lemma excitation_cov (hr : R.Realizes (W:=W) X rs) (v : S.Union) (f : Probe E4) (g : Poincare) :
    R.action.V g (excitation R.operators v f) =
      excitation R.operators (R.spin.rail g.Λ v) (Joint.push g f) := by
    unfold excitation Fields.vector; rw [Fields.evaluates,Fields.evaluates,Fields.edits,
      hr.covariance.covariance]
    dsimp only
    change ((R.operators.field _ _) _).val=((R.operators.field _ _) _).val
    congr 2
    apply Subtype.ext; exact hr.covariance.vacuum _

lemma excitation_trans (hr : R.Realizes (W:=W) X rs) (v : S.Union) (f : Probe E4) (b : E4) :
    R.action.orbit.translation b (excitation R.operators v f) =
      excitation R.operators v (Joint.push (Poincare.translation b) f) := by
    rw [show R.action.orbit.translation b=R.action.V (Poincare.translation b) from rfl,excitation_cov hr]; simp [Poincare.translation,hr.letters.identity]

lemma mass_read (h : Bid.Hull B F R.J) (hm : F.Breathes) (he : F.Opens W)
    (hr : R.Realizes (W:=W) X rs) (v : S.Union) (f : Probe E4) :
    R.momentum.diagonal (excitation R.operators v f) =
      (spectralMeasure B v).withDensity fun p => (probeWeight f p : ℝ≥0∞) := by
    let μ := spectralMeasure B v
    haveI ht : μ.HasTemperateGrowth := spectral_temperate h hm v
    change _=μ.withDensity _
    haveI hi : IsFiniteMeasure (μ.withDensity fun p => (probeWeight f p : ℝ≥0∞)) := by
        apply isFiniteMeasure_withDensity
        have hh := ((testPlus f).memLp 2 μ).norm.integrable_sq.hasFiniteIntegral
        unfold HasFiniteIntegral at hh
        simp only [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at hh
        simpa [probeWeight,enorm_eq_nnnorm,lt_top_iff_ne_top] using hh
    apply Measure.ext_of_charFun; ext1 b
    rw [hr.spectral, excitation_trans hr,norm_read h hm he hr,charFun_apply,
        integral_withDensity_eq_integral_smul (probe_cont f).measurable]
    apply integral_congr_ae; filter_upwards with p
    rw [test_trans]; let z := testPlus f p
    change star z * (Probe.plane p b * z) = ((probeWeight f p : ℝ≥0):ℝ) • Probe.plane p b
    rw [Complex.real_smul]; unfold probeWeight
    change star z*(Probe.plane p b*z)= (↑(((‖z‖₊^2:ℝ≥0):ℝ)):ℂ)*_
    rw [NNReal.coe_pow,coe_nnnorm, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,Complex.star_def]
    ring

lemma testPlus_onto : Function.Surjective (testPlus (V:=E4)) := by
    intro f
    let a : ℂ := Probe.pref E4
    have h : a ≠ 0 := Complex.ofReal_ne_zero.mpr Probe.prepos.ne'
    refine ⟨Probe.hat (a⁻¹ • f),?_⟩
    rw [testPlus, _root_.smul_apply, Probe.comes, smul_smul]; rw [mul_inv_cancel₀ h,one_smul]

lemma probe_one (m : ℕ) : ∃ f : Probe E4, ∀ p∈closedBall (0:E4) (m:ℝ), probeWeight f p = 1 := by
    let B : ContDiffBump (0:E4) := ⟨(m:ℝ)+1,(m:ℝ)+2,by positivity,by linarith⟩
    let v : Probe E4 := (B.hasCompactSupport.comp_left (show Complex.ofReal 0=0 by norm_cast)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp B.contDiff)
    obtain ⟨f,hf⟩ := testPlus_onto v
    refine ⟨f, fun p hp => ?_⟩
    unfold probeWeight; rw [hf]; change ‖(↑(B p):ℂ)‖₊ ^ 2=_
    rw [B.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (by unfold B; simp) hp)]
    simp

lemma local_weight {m : ℕ} {f : Probe E4} (h : ∀ p ∈ closedBall (0:E4) (m:ℝ), probeWeight f p = 1)
    (μ : Measure E4) {A : Set E4} (ha : MeasurableSet A) (hp : A ⊆ closedBall 0 (m:ℝ)) :
    (μ.withDensity fun p => (probeWeight f p : ℝ≥0∞)) A = μ A := by
    rw [withDensity_apply _ ha, setLIntegral_congr_fun (g:=fun _ => 1) ha ?_,setLIntegral_one]
    exact fun x hx => by simp [h x (hp hx)]

lemma weights_injective (μ ν : Measure E4) (hw : ∀ f : Probe E4, (μ.withDensity fun p => (probeWeight f p : ℝ≥0∞)) =
    ν.withDensity fun p => (probeWeight f p : ℝ≥0∞)) : μ = ν := by
    ext A ha
    let D (m:ℕ) := A ∩ closedBall (0:E4) (m:ℝ)
    have he : ⋃ m, D m=A := by simp [D, ← inter_iUnion,iUnion_closedBall_nat]
    have ht (m) : μ (D m)=ν (D m) := by
        obtain ⟨f,hf⟩ := probe_one m
        rw [← local_weight hf μ (ha.inter isClosed_closedBall.measurableSet) inter_subset_right,
            ← local_weight hf ν (ha.inter isClosed_closedBall.measurableSet) inter_subset_right,hw]
    have hm : Monotone D := fun i j hj => inter_subset_inter_right A (closedBall_subset_closedBall (Nat.cast_le.mpr hj))
    refine tendsto_nhds_unique_of_eventuallyEq (f:=fun i => μ (D i)) (g:=fun i => ν (D i)) (l:=atTop) ?_ ?_ (Eventually.of_forall ht)
    · simpa only [← Function.comp_def,he] using tendsto_measure_iUnion_atTop (μ := μ) hm
    · simpa only [← Function.comp_def,he] using tendsto_measure_iUnion_atTop (μ := ν) hm

lemma spectral_forward (h : Bid.Hull B F R.J) (hm : F.Breathes) (he : F.Opens W)
    (hr : R.Realizes (W:=W) X rs) (v : S.Union) : spectralMeasure B v coneᶜ = 0 := by
    let D := coneᶜ
    let μ := spectralMeasure B v
    have hd : MeasurableSet D := Mink.closed_cone.measurableSet.compl
    change μ D = 0
    have ht (f : Probe E4) : (μ.withDensity fun p => (probeWeight f p : ℝ≥0∞)) D = 0 := by
        rw [show μ=spectralMeasure B v from rfl, ← mass_read h hm he hr, PVM.null_pair]
        · rw [show D=coneᶜ from rfl,hr.forward]; rfl
        exact hd
    have hh : ⋃ m : ℕ, D ∩ closedBall 0 (m:ℝ)=D := by rw [← inter_iUnion,iUnion_closedBall_nat, inter_univ]
    rw [← hh]; refine measure_iUnion_null fun i => ?_
    obtain ⟨f,hf⟩ := probe_one i
    rw [← local_weight hf μ (hd.inter isClosed_closedBall.measurableSet) inter_subset_right]
    exact measure_mono_null inter_subset_left (ht f)

lemma test_motion (f : Probe E4) (g : Lorentz) (p : E4) :
    testPlus (Joint.push (Poincare.motion g) f) (g.dual.act p)=testPlus f p := by
    rw [testPlus_apply,testPlus_apply, ← g.preserves.integral_comp g.sends.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
    congr! 1; ext x
    simp [Joint.push_at,Probe.plane, Lorentz.dual_sent,Poincare.motion]

lemma spectral_placed (h : Bid.Hull B F R.J) (hm : F.Breathes) (he : F.Opens W)
    (hr : R.Realizes (W:=W) X rs) (v : S.Union) (g : Lorentz) :
    spectralMeasure B (R.spin.rail g v) = (spectralMeasure B v).map (g.dual.act) := by
    have hp (x : R.operators.H) : R.momentum.diagonal x=R.action.μ x := by
        apply Measure.ext_of_charFun; ext1 b; rw [hr.spectral,Action.μ,R.action.orbit.total]
    apply weights_injective _ _
    intro f
    let t := Joint.push (Poincare.motion g)⁻¹ f
    have ht : Joint.push (Poincare.motion g) t=f := by
        ext1 x; unfold t; rw [Joint.push_at,Joint.push_at]
        congr 1; rw [← Poincare.sends_mul, inv_inv, mul_inv_cancel, Poincare.sends_one]
    let μ := spectralMeasure B v
    have hh := R.action.placed g (excitation R.operators v t)
    rw [← hp, ← hp, excitation_cov hr, mass_read h hm he hr, mass_read h hm he hr, ht] at hh
    change (spectralMeasure B (R.spin.rail g v)).withDensity _ = _ at hh
    rw [hh]; ext A hA
    have ha := g.dual.act.continuous.measurable
    rw [withDensity_apply _ hA,setLIntegral_map hA (probe_meas f) ha,map_apply ha hA,withDensity_apply _ (ha hA)]
    apply setLIntegral_congr_fun (ha hA); intro x hx
    unfold probeWeight; rw [← ht]; dsimp only; rw [test_motion]
end YM.TraceExtension
