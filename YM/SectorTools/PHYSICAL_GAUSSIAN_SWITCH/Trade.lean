import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Relative
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Kernel


/-!
# Exact real-exponent Lp comparison in SectorChange coordinates

A,D are covariances (actual counting `Table`s). In `trade A D h z`
(Relative.lean), `z` is under the REFERENCE `Gaussian.cloud D`, and
`h` = reference mean MINUS target mean (same coupling units as z).
All determinants in counting conventions; prices below are MOMENTS,
so remember the `1/p` power in using with Hölder.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment.Relative (trade)
open scoped Topology BigOperators ENNReal
local notation "Covar" => Next.SectorChange.Gaussian.Table

variable {I : Type} [Fintype I] [DecidableEq I]

section auxiliary
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {F L : X → ℝ} {E : Type*} [NormedAddCommGroup E]

lemma mem_by_norm {f : X → E} (hm : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    MemLp f (ENNReal.ofReal p) μ ↔ Integrable (fun x => ‖f x‖ ^ p) μ := by
  have h := integrable_norm_rpow_iff (p:=ENNReal.ofReal p) hm
    ((ENNReal.ofReal_pos.mpr hp).ne') ENNReal.ofReal_ne_top
  rwa [ENNReal.toReal_ofReal hp.le,Iff.comm] at h

lemma mem_by_rpow (hm : Measurable L) (hl : ∀ x, 0 ≤ L x) {p : ℝ} (hp : 0 < p) :
    MemLp L (ENNReal.ofReal p) μ ↔ Integrable (fun x => L x ^ p) μ := by
  simp_rw [mem_by_norm hm.aestronglyMeasurable hp,Real.norm_of_nonneg (hl _)]





variable [NormedSpace ℝ E]
/-- Keep integrability as well; this is not a bound obtained by interpreting
an undefined density comparison as an integral. -/
lemma holder_step {f : X → E} {p : ℝ} (hp : 1<p) (hm : MemLp L (ENNReal.ofReal p) μ) (hl : ∀ x, 0 ≤ L x)
    (hf : MemLp f (ENNReal.ofReal (Real.conjExponent p)) μ) :
    let q := Real.conjExponent p
    Integrable (fun x => L x • f x) μ ∧
      ‖∫ x,L x • f x ∂μ‖ ≤ (∫ x, L x ^ p ∂μ) ^ (1/p) * (∫ x, ‖f x‖ ^ q ∂μ) ^ (1/q) := by
  intro q
  have he := Real.HolderConjugate.conjExponent hp
  haveI := he.ennrealOfReal
  refine ⟨memLp_one_iff_integrable.mp (hf.smul hm), (norm_integral_le_integral_norm _).trans ?_⟩
  simp_rw [norm_smul,Real.norm_of_nonneg (hl _)]
  exact integral_mul_le_Lp_mul_Lq_of_nonneg he (Eventually.of_forall hl) (Eventually.of_forall fun _ => norm_nonneg _) hm hf.norm
end auxiliary

variable {A D : Covar I} {h : Vec I} {p : ℝ}
lemma trade_pos (hA : A.PosDef) (hD : D.PosDef) (h z : Vec I) : 0 < trade A D h z :=
  mul_pos (div_pos (Real.sqrt_pos.mpr hD.det_pos) (Real.sqrt_pos.mpr hA.det_pos)) (Real.exp_pos _)
lemma trade_cont (A D : Covar I) (h : Vec I) : Continuous (trade A D h) := by
  unfold trade force Matrix.mulVec dotProduct; fun_prop

/-- Factor in front of the variable quadratic+linear potential (NOT
changing the normalizer to its reciprocal). -/
def tax (A D : Covar I) (h : Vec I) :=
  Real.sqrt D.det / Real.sqrt A.det * Real.exp (-quad A⁻¹ h/2)
lemma tax_pos (hA : A.PosDef) (hD : D.PosDef) (h : Vec I) : 0 < tax A D h :=
  mul_pos (div_pos (Real.sqrt_pos.mpr hD.det_pos) (Real.sqrt_pos.mpr hA.det_pos)) (Real.exp_pos _)

lemma trade_as_potential (hA : A.PosDef) (D : Covar I) (h z : Vec I) :
    trade A D h z = tax A D h * kernel (A⁻¹-D⁻¹) (-(A⁻¹ *ᵥ h)) z := by
  unfold trade tax kernel
  rw [mul_assoc,← Real.exp_add]
  unfold force exponent
  change _ * Real.exp ((quad D⁻¹ z-quad A⁻¹ (h+z))/2) = _
  rw [quad_add (symm_pos hA.inv),quad_diff,neg_dotProduct,dotProduct_comm (A⁻¹ *ᵥ h) z,
    turn (symm_pos hA.inv) z h]
  ring_nf

def mixed (A D : Covar I) (p : ℝ) := p • A⁻¹ + (1-p) • D⁻¹
def debt (A : Covar I) (p : ℝ) (h : Vec I) := (-p) • (A⁻¹ *ᵥ h)

def price (A D : Covar I) (p : ℝ) (h : Vec I) :=
  (Real.sqrt D.det / Real.sqrt A.det)^p *
    (Real.sqrt ((mixed A D p)⁻¹).det / Real.sqrt D.det) *
      Real.exp ((quad (mixed A D p)⁻¹ (debt A p h)-p*quad A⁻¹ h)/2)

lemma mixed_symm (hA : A.PosDef) (hD : D.PosDef) : (mixed A D p).IsSymm := by
  unfold mixed Matrix.IsSymm; rw [transpose_add,transpose_smul,transpose_smul,(symm_pos hA.inv).eq,(symm_pos hD.inv).eq]

section volume
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Under the probability law; `ratio` here is the accepted Lebesgue density. -/
lemma through_volume (hD : D.PosDef) (f : Vec I → E) :
    (Integrable f (cloud D) ↔ Integrable (fun z => ratio D z • f z)) ∧
      (∫ z,f z ∂cloud D) = ∫ z,ratio D z • f z := by
  rw [cloud_formula hD,
    integrable_withDensity_iff_integrable_smul' ((measurable_ratio _).ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul ((measurable_ratio _).ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (ratio_pos hD _).le]; trivial

private def receipt (A D : Covar I) (p : ℝ) (h : Vec I) := tax A D h ^ p / coat D
private lemma receipt_pos (hA : A.PosDef) (hD : D.PosDef) : 0 < receipt A D p h :=
  div_pos (Real.rpow_pos_of_pos (tax_pos hA hD h) _) (coat_pos hD)

private lemma volume_entry (hA : A.PosDef) (hD : D.PosDef) (z : Vec I) :
    ratio D z * trade A D h z ^ p = receipt A D p h * kernel (mixed A D p) (debt A p h) z := by
  have he : -force D z/2 + exponent (A⁻¹-D⁻¹) (-(A⁻¹ *ᵥ h)) z * p = exponent (mixed A D p) (debt A p h) z := by
    unfold force exponent mixed debt
    change -quad D⁻¹ z/2 + _ = _
    rw [quad_sum,quad_smul,quad_smul,quad_diff,neg_dotProduct,smul_dotProduct,smul_eq_mul]; ring
  rw [trade_as_potential hA, Real.mul_rpow (tax_pos hA hD _).le (kernel_pos ..).le,ratio]
  unfold kernel receipt
  rw [← Real.exp_mul,← he,Real.exp_add]; ring
end volume

theorem trade_integrable_iff (hA : A.PosDef) (hD : D.PosDef) :
    Integrable (fun z => trade A D h z ^ p) (cloud D) ↔ (mixed A D p).PosDef := by
  rw [(through_volume hD _).1]
  simp_rw [smul_eq_mul, volume_entry hA hD]
  let k := receipt A D p h
  have hk : k ≠ 0 := (receipt_pos hA hD).ne'
  let f := kernel (mixed A D p) (debt A p h)
  change Integrable (fun z => k*f z) ↔ _
  rw [← kernel_integrable_iff (mixed_symm hA hD) (debt A p h)]
  constructor
  · intro ht
    simpa [← mul_assoc,hk] using! ht.const_mul k⁻¹
  intro ht; exact ht.const_mul k

theorem trade_mem_iff (hA : A.PosDef) (hD : D.PosDef) (hp : 0<p) :
    MemLp (trade A D h) (ENNReal.ofReal p) (cloud D) ↔ (mixed A D p).PosDef := by
  rw [mem_by_rpow (trade_cont ..).measurable (fun _ => (trade_pos hA hD _ _).le) hp, trade_integrable_iff hA hD]

/-- Exact integral (positive moment) in the admissible case. -/
theorem trade_integral (hA : A.PosDef) (hD : D.PosDef) (he : (mixed A D p).PosDef) :
    (∫ z, trade A D h z ^ p ∂ cloud D) = price A D p h := by
  rw [(through_volume hD _).2]
  simp_rw [smul_eq_mul, volume_entry hA hD]; rw [integral_const_mul,(kernel_paid he _).2]
  have hr : 0 < Real.sqrt D.det / Real.sqrt A.det := div_pos (Real.sqrt_pos.mpr hD.det_pos) (Real.sqrt_pos.mpr hA.det_pos)
  have hi : (quad (mixed A D p)⁻¹ (debt A p h) - p * quad A⁻¹ h)/2 =
      -quad A⁻¹ h /2 * p + quad (mixed A D p)⁻¹ (debt A p h) / 2 := by ring
  rw [receipt,tax,Real.mul_rpow hr.le (Real.exp_pos _).le, ← Real.exp_mul,price,hi,Real.exp_add]
  unfold coat
  field_simp [(show 0 < dome I from dome_pos).ne']





lemma normalized_trade (hA : A.PosDef) (hD : D.PosDef) (h : Vec I) :
    Integrable (trade A D h) (cloud D) ∧ (∫ z, trade A D h z ∂cloud D) = 1 := by
  obtain ⟨hh,he⟩ := AnalyticBridge.GaussianFieldAlignment.Relative.change hA hD h (fun _ => (1:ℝ))
  simp only [smul_eq_mul,mul_one] at hh he; exact ⟨hh.mp (integrable_const _), by simpa using he.symm⟩

/-- Consume the *actual* accepted identity. `hf` sees h+z under D,
not just z under D. -/
theorem trade_comparison {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hA : A.PosDef) (hD : D.PosDef) (hp : 1<p) (he : (mixed A D p).PosDef)
    {f : Vec I → X} (hf : MemLp (fun z => f (h+z)) (ENNReal.ofReal (Real.conjExponent p)) (cloud D)) :
    let q := Real.conjExponent p
    Integrable f (cloud A) ∧
      ‖∫ z,f z ∂cloud A‖ ≤ price A D p h ^ (1/p) * (∫ z, ‖f (h+z)‖ ^ q ∂cloud D) ^ (1/q) := by
  obtain ⟨ha,hb⟩ := AnalyticBridge.GaussianFieldAlignment.Relative.change hA hD h f
  obtain ⟨ht,hi⟩ := holder_step hp ((trade_mem_iff (h:=h) hA hD (zero_lt_one.trans hp)).mpr he)
    (fun _ => (trade_pos hA hD _ _).le) hf
  rw [trade_integral hA hD he] at hi
  intro q; rw [ha,hb]; exact ⟨ht,hi⟩
end YM.SectorTools.PhysicalGaussianSwitch
