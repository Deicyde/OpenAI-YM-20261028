import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Blocks

/-!
# Real centered reference measure on the regular Z's. Physical counting

Finite matrices; normalize including the determinant. This uses the
**one** joint law (E Lemma on shared invocations). Costs through the
precision gap, *not scaling that gap with the period*. Tilt estimate in
next file. Invoicing without any tacit Lebesgue-volume convention
for `.order` or Lie coordinates -- here use one copy per real orthonormal
Lie coordinate, connect to Haar/exponential chart separately.

Tangent entry indices may be empty (can likewise complete the arrays
first with identity matrices on inactive coordinates).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Centered
open Function MeasureTheory Filter Matrix 
 
open scoped Topology BigOperators ENNReal Matrix.Norms.Frobenius
variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- Here `A` is precision, i.e. inverse of our chosen centered covariance. -/
def heat (A : Matrix n n ℝ) (z : n → ℝ) := Real.exp (-(dotProduct z (A *ᵥ z))/2)

omit [DecidableEq n] in
lemma heat_continuous (A : Matrix n n ℝ) : Continuous (heat A) := by
  unfold heat dotProduct Matrix.mulVec
  simp only [dotProduct]; fun_prop

def unitVolume : ℝ := Real.sqrt (2*Real.pi)

lemma unit_pos : 0 < unitVolume := by unfold unitVolume; positivity

def bill (A : Matrix n n ℝ) : ℝ := unitVolume^(Fintype.card n) * Real.exp (-Real.log A.det/2)

lemma bill_pos (A : Matrix n n ℝ) : 0 < bill A := by unfold bill; have h := unit_pos; positivity

private lemma identity_mass (n : Type*) [Fintype n] [DecidableEq n] :
    (∫ z : n → ℝ, heat 1 z) = unitVolume^(Fintype.card n) := by
  let f (x : ℝ) := Real.exp (-(1/2)*x^2)
  have h z : heat (1:Matrix n n ℝ) z = ∏ i, f (z i) := by
    unfold f heat dotProduct; rw [Matrix.one_mulVec, ← Real.exp_sum, ← Finset.mul_sum]
    simp_rw [pow_two]; ring_nf
  have hf : (∫ w, f w) = unitVolume := by
    dsimp only [f]; rw [integral_gaussian]
    unfold unitVolume; ring_nf
  simp_rw [h]; rw [integral_fintype_prod_volume_eq_pow (ι:=n) f,hf]

open scoped MatrixOrder in
private lemma obtain_root (hp : A.PosDef) : ∃ B : Matrix n n ℝ, B.transpose * B = A := by
  obtain ⟨B,hg⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp.posSemidef.nonneg
  exact ⟨B,hg.symm⟩

/-- Real change of variables -- no open choices of volume; SPD sufficient. -/
theorem Gaussian_bill (hp : A.PosDef) : (∫ z : n → ℝ, heat A z) = bill A := by
  obtain ⟨B,hB⟩ := obtain_root hp
  have hs : B.det^2=A.det := by rw [← hB,Matrix.det_mul,Matrix.det_transpose,sq]
  have ht := hp.det_pos
  have hb : B.det ≠ 0 := by intro he; rw [he,zero_pow (by decide)] at hs; exact ht.ne hs
  let f := fun x : n → ℝ => (Matrix.toLin' B) x
  have hf : Measurable f := (LinearMap.continuous_of_finiteDimensional _).measurable
  have hw : Measure.map f volume = ENNReal.ofReal |B.det⁻¹| • volume :=
    Real.map_matrix_volume_pi_eq_smul_volume_pi hb
  have he : ∀ z : n → ℝ, heat A z = heat 1 (f z) := by
    intro z; unfold heat; rw [← hB, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, Matrix.one_mulVec]; rfl
  have hu : Real.exp (-Real.log A.det/2) = |B.det⁻¹| := by
    have hi : A.det=|B.det|^2 := ((hs.symm.trans (sq_abs B.det).symm))
    rw [hi, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [show -(2*_) / 2 = - Real.log |B.det| by ring, Real.exp_neg, Real.exp_log (abs_pos.mpr hb), abs_inv]
  calc
    _ = ∫ z : n → ℝ, heat 1 (f z) := by simp_rw [he]
    _ = ∫ z, heat 1 z ∂Measure.map f volume := (integral_map hf.aemeasurable (heat_continuous _).aestronglyMeasurable).symm
    _ = _ := by rw [hw, MeasureTheory.integral_smul_measure,identity_mass,bill, hu,
                    ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,mul_comm]

lemma heat_integrable (hp : A.PosDef) : Integrable (heat A) :=
  .of_integral_ne_zero ((Gaussian_bill hp) ▸ (bill_pos _).ne')

def density (A : Matrix n n ℝ) (z : n → ℝ) := (bill A)⁻¹ * heat A z

def law (A : Matrix n n ℝ) : Measure (n → ℝ) := volume.withDensity fun x => ENNReal.ofReal (density A x)

lemma density_pos (A : Matrix n n ℝ) (z : n → ℝ) : 0 < density A z :=
  mul_pos (inv_pos.mpr (bill_pos A)) (Real.exp_pos _)

lemma density_measurable (A : Matrix n n ℝ) : Measurable (density A) :=
  (measurable_const.mul (heat_continuous A).measurable)

lemma normalized (hp : A.PosDef) : (∫ z, density A z) = 1 := by
  unfold density; rw [integral_const_mul,Gaussian_bill hp, inv_mul_cancel₀ (bill_pos _).ne']

lemma probability (hp : A.PosDef) : IsProbabilityMeasure (law A) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal, normalized hp, ENNReal.ofReal_one]
  · exact (heat_integrable hp).const_mul _
  filter_upwards with x using (density_pos A x).le

lemma integrates {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : Matrix n n ℝ)
    (g : (n → ℝ) → X) : (∫ z, g z ∂law A) = ∫ z, density A z • g z := by
  simp only [law, integral_withDensity_eq_integral_toReal_smul (density_measurable _).ennreal_ofReal
    (show ∀ᵐ z ∂volume, ENNReal.ofReal (density A z)<⊤ from Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_ofReal (density_pos ..).le]

lemma pays_L1 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : Matrix n n ℝ)
    (g : (n → ℝ) → X) : Integrable g (law A) ↔ Integrable (fun z => density A z • g z) := by
  let b := fun z => Real.toNNReal (density A z)
  have he : Measurable b := (density_measurable _).real_toNNReal
  rw [law]; change Integrable g (volume.withDensity (fun z => (b z:ℝ≥0∞))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul he]
  congr! 2 with z
  change (b z:ℝ) • g z = _
  rw [show (b z:ℝ) = density A z from Real.coe_toNNReal _ (density_pos ..).le]
end YM.AnalyticNext.ConnectedActivity.Centered
