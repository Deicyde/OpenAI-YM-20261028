import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Variation

/-!
# In the physical reads

Retain exact laws in both unit systems. To return to unscaled reads,
carry g and the ideal mean on the *same slots*, no uniform-temperature
assumption on this part of the theorem. These are still the Gaussian
comparisons, before any profile multiplier or integration over tags/Y.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546
open MeasureTheory Function Filter
open YM.Next.SectorChange.Gaussian YM.SectorTools.PhysicalGaussianSwitch
open YM.AnalyticBridge.LocalGaussianLaws
open scoped Topology
local notation "Covar" => YM.Next.SectorChange.Gaussian.Table
variable {I n m : Type}

def physicalRead (a : Vec n) (g : ℝ) (e : I ↪ n) (z : Vec n) := (a + g • z) ∘ e

def inUnits (b : Vec I) (g : ℝ) (x : Vec I) := g⁻¹ • (x - b)
def restore (b : Vec I) (g : ℝ) (z : Vec I) := b + g • z

lemma inUnits_restore (b : Vec I) {g : ℝ} (hg : g ≠ 0) (z : Vec I) :
    inUnits b g (restore b g z) = z := by
  unfold inUnits restore
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hg, one_smul]
lemma restore_inUnits (b : Vec I) {g : ℝ} (hg : g ≠ 0) (z : Vec I) :
    restore b g (inUnits b g z) = z := by
  unfold inUnits restore
  rw [smul_smul, mul_inv_cancel₀ hg, one_smul, add_sub_cancel]

/-- `δ`, sign **target minus ideal**. -/
def displacement (a : Vec n) (b : Vec m) (g : ℝ) (e : I ↪ n) (l : I ↪ m) :=
  g⁻¹ • (a ∘ e - b ∘ l)

lemma against (a : Vec n) (b : Vec m) (g : ℝ) (e : I ↪ n) (l : I ↪ m) :
    -displacement a b g e l = g⁻¹ • (b ∘ l - a ∘ e) := by
  unfold displacement
  rw [← smul_neg, neg_sub]

lemma readUnits_target (a : Vec n) (b : Vec m) {g : ℝ} (hg : g ≠ 0) (e : I ↪ n) (l : I ↪ m)
    (z : Vec n) :
    inUnits (b ∘ l) g (physicalRead a g e z) = displacement a b g e l + z ∘ e := by
  unfold inUnits displacement physicalRead
  change g⁻¹ • (a ∘ (e:I→n) + g • (z ∘ (e:I→n)) - b ∘ (l:I→m)) = _
  rw [add_sub_right_comm, smul_add, smul_smul, inv_mul_cancel₀ hg, one_smul]

lemma readUnits_ideal (b : Vec m) {g : ℝ} (hg : g ≠ 0) (l : I ↪ m) (z : Vec m) :
    inUnits (b ∘ l) g (physicalRead b g l z) = z ∘ l :=
  inUnits_restore (b ∘ l) hg (z ∘ l)

lemma restore_meas (b : Vec I) (g : ℝ) : Measurable (restore b g) := by
  unfold restore
  fun_prop
lemma inUnits_meas (b : Vec I) (g : ℝ) : Measurable (inUnits b g) := by
  unfold inUnits
  fun_prop
lemma physicalRead_meas (a : Vec n) (g : ℝ) (e : I ↪ n) : Measurable (physicalRead a g e) := by
  apply measurable_pi_lambda; intro i
  change Measurable (fun z : Vec n => a (e i) + g * z (e i))
  fun_prop

variable [Fintype n] [DecidableEq n] [Fintype I]

def readLaw (Q : Covar n) (a : Vec n) (g : ℝ) (e : I ↪ n) :=
  (cloud Q).map (physicalRead a g e)

omit [Fintype I] in
lemma readMap (Q : Covar n) (a : Vec n) (g : ℝ) (e : I ↪ n) :
    MeasurePreserving (physicalRead a g e) (cloud Q) (readLaw Q a g e) :=
  ⟨physicalRead_meas .., rfl⟩

omit [Fintype I] in
lemma renormalizing (Q : Covar n) (a : Vec n) (g : ℝ) (e : I ↪ n) {μ : Measure (Vec I)}
    (b : Vec I) (h : MeasurePreserving (inUnits b g ∘ physicalRead a g e) (cloud Q) μ) :
    MeasurePreserving (inUnits b g) (readLaw Q a g e) μ := by
  refine ⟨inUnits_meas ..,?_⟩
  unfold readLaw; rw [Measure.map_map (inUnits_meas ..) (physicalRead_meas ..), h.map_eq]

omit [Fintype I] in
lemma restored (Q : Covar n) (a : Vec n) {g : ℝ} (hg : g ≠ 0) (e : I ↪ n) {μ : Measure (Vec I)}
    (b : Vec I) (h : MeasurePreserving (inUnits b g ∘ physicalRead a g e) (cloud Q) μ) :
    MeasurePreserving (restore b g) μ (readLaw Q a g e) := by
  refine ⟨restore_meas ..,?_⟩
  rw [← h.map_eq, Measure.map_map (restore_meas ..) h.measurable]
  simp_rw [comp_def, restore_inUnits b hg]; rfl

/-- Pay explicitly to go to unscaled physical reads. -/
def readFee (b : Vec I) (g : ℝ) : ℝ := 1 + ‖b‖ + |g|
lemma readFee_nn (b : Vec I) (g : ℝ) : 0 ≤ readFee b g := by unfold readFee; positivity

lemma weight_restore (b : Vec I) (g : ℝ) (z : Vec I) (q : ℕ) :
    weight q (restore b g z) ≤ readFee b g ^ q * weight q z := by
  have h := norm_add_le b (g • z)
  rw [norm_smul, Real.norm_eq_abs] at h
  unfold weight restore readFee
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [norm_nonneg b, norm_nonneg z, abs_nonneg g]

lemma TestPrice.restored {X : Type*} [NormedAddCommGroup X] {F : Vec I → X}
    {c : ℝ} {D : ℕ} (h : TestPrice F D c) (b : Vec I) (g : ℝ) :
    TestPrice (fun z => F (restore b g z)) D (c * readFee b g ^ D) := by
  refine ⟨mul_nonneg h.nonneg (pow_nonneg (readFee_nn ..) _),
    h.measurable.comp_measurable (restore_meas ..),fun z => ?_⟩
  rw [mul_assoc]
  exact (h.size _).trans (mul_le_mul_of_nonneg_left (weight_restore ..) h.nonneg)

lemma MomentBound.physical {μ ν : Measure (Vec I)} {q : ℕ} {A : ℝ} (h : MomentBound μ q A)
    (b : Vec I) (g : ℝ) (hr : MeasurePreserving (restore b g) μ ν) :
    MomentBound ν q (readFee b g ^ q * A) := by
  let r := readFee b g ^ q
  have hp := h.auth.const_mul r
  have hf := pay_pull hr (weight q) (weight_continuous _).aestronglyMeasurable
  have hi : Integrable (fun z => weight q (restore b g z)) μ := hp.mono'
    (((weight_continuous _).measurable.comp (restore_meas ..)).aestronglyMeasurable)
    (Eventually.of_forall (fun z => (Real.norm_of_nonneg (weight_nonneg _ _)).trans_le (weight_restore ..)))
  refine ⟨hf.1.mp hi,?_⟩
  rw [← hf.2]
  apply (integral_mono hi hp (fun z => weight_restore b g z q)).trans
  rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left h.bound (pow_nonneg (readFee_nn ..) _)

variable [DecidableEq I] [Fintype m] [DecidableEq m]

/-- A bill for the actual coordinates, including which projection is
being used in *each* of the systems. In physical deployment `l` always
uses the load map after `e`. -/
structure ReadPrice (Q : Covar n) (J : Covar m) (a : Vec n) (b : Vec m) (g : ℝ)
    (e : I ↪ n) (l : I ↪ m) (x U : ℝ) : Prop where
  Q_pos : Q.PosDef
  J_pos : J.PosDef
  g_pos : 0 < g
  paid : PairPrice (Q.submatrix e e) (J.submatrix l l) (displacement a b g e l) x U

variable {Q : Covar n} {J : Covar m} {a : Vec n} {b : Vec m} {g : ℝ} {e : I ↪ n}
    {l : I ↪ m} {x U : ℝ}
namespace ReadPrice
variable (h : ReadPrice Q J a b g e l x U)
include h

set_option linter.unusedSectionVars false in
-- Keep both index spaces finite even in these one-sided projections.
theorem targetLaw :
    MeasurePreserving (inUnits (b ∘ l) g ∘ physicalRead a g e) (cloud Q)
      (shift (Q.submatrix e e) (displacement a b g e l)) := by
  have hp := AnalyticBridge.GaussianFieldAlignment.Completed.marginal e h.Q_pos.posSemidef
  have he := to_shift (Q.submatrix e e) (displacement a b g e l)
  rw [show (inUnits (b ∘ l) g ∘ physicalRead a g e) = fun z => displacement a b g e l + z ∘ e from
    funext (readUnits_target a b (ne_of_gt h.g_pos) e l)]
  exact he.comp hp

set_option linter.unusedSectionVars false in
theorem idealLaw :
    MeasurePreserving (inUnits (b ∘ l) g ∘ physicalRead b g l) (cloud J) (cloud (J.submatrix l l)) := by
  rw [show (inUnits (b ∘ l) g ∘ physicalRead b g l) = fun z => z ∘ l from
    funext (readUnits_ideal b (ne_of_gt h.g_pos) l)]
  exact AnalyticBridge.GaussianFieldAlignment.Completed.marginal l h.J_pos.posSemidef

theorem returnTarget :
    MeasurePreserving (restore (b ∘ l) g) (shift (Q.submatrix e e) (displacement a b g e l))
      (readLaw Q a g e) :=
  restored Q a (ne_of_gt h.g_pos) e (b ∘ l) h.targetLaw

theorem returnIdeal :
    MeasurePreserving (restore (b ∘ l) g) (cloud (J.submatrix l l))
      (readLaw J b g l) :=
  restored J b (ne_of_gt h.g_pos) l (b ∘ l) h.idealLaw

theorem rawMoments {K : ℕ} (hK : Fintype.card I ≤ K) (q : ℕ) :
    let A := readFee (b ∘ l) g ^ q * momentPrice K q U 1
    MomentBound (readLaw Q a g e) q A ∧ MomentBound (readLaw J b g l) q A := by
  intro A
  obtain ⟨h1,h2⟩ := h.paid.moments hK q
  exact ⟨h1.physical _ _ h.returnTarget, h2.physical _ _ h.returnIdeal⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Vec I → E} {D : ℕ} {c : ℝ}

/-- Comparison on the full ambient systems, with explicit physical
centering and scaling to the fluctuation units. Includes the integrable
normalized likelihood identity on the marginal. -/
theorem onFull [CompleteSpace E] {K : ℕ} (hK : Fintype.card I ≤ K) (hF : TestPrice F D c) :
    let C := Q.submatrix e e
    let B := J.submatrix l l
    let δ := displacement a b g e l
    let f := inUnits (b ∘ l) g ∘ physicalRead a g e
    let j := inUnits (b ∘ l) g ∘ physicalRead b g l
    Integrable (F ∘ f) (cloud Q) ∧ Integrable (F ∘ j) (cloud J) ∧
      Integrable (fun z => Density.replace C B (-δ) z • F z) (cloud B) ∧
      (∫ z, F (f z) ∂cloud Q) = (∫ z, Density.replace C B (-δ) z • F z ∂cloud B) ∧
      ‖(∫ z, F (f z) ∂cloud Q) - ∫ z, F (j z) ∂cloud J‖ ≤ c * errorFare K D U x := by
  intro C B δ f j
  obtain ⟨ht, hb, hr⟩ := h.paid.comparing hK hF
  obtain ⟨ht',h1⟩ := pay_pull h.targetLaw F ht.auth.aestronglyMeasurable
  obtain ⟨hb',h2⟩ := pay_pull h.idealLaw F hb.auth.aestronglyMeasurable
  obtain ⟨he,h3⟩ := h.paid.exchange F
  refine ⟨ht'.mpr ht.auth, hb'.mpr hb.auth, he.mp ht.auth, h1.trans h3,?_⟩
  unfold f j; rw [h1,h2]
  exact hr

/-- Raw/unscaled physical read comparison (again on the **full** two systems).
Still polynomial cost since K,D are fixed, but not claiming a limit over
admissible beta without the raw scale and mean. Also produces moments/tails
on the associated two physical read laws. -/
theorem raw [CompleteSpace E] {K : ℕ} (hK : Fintype.card I ≤ K) (hF : TestPrice F D c) :
    let C := Q.submatrix e e
    let B := J.submatrix l l
    let δ := displacement a b g e l
    let f := physicalRead a g e
    let j := physicalRead b g l
    let L := Density.replace C B (-δ)
    let R := restore (b ∘ l) g
    let q := highMoment D
    let r := readFee (b ∘ l) g
    let A := r ^ q * momentFare K D U
    TailPrice (readLaw Q a g e) F q D A c ∧ TailPrice (readLaw J b g l) F q D A c ∧
      Integrable (F ∘ f) (cloud Q) ∧ Integrable (F ∘ j) (cloud J) ∧
      Integrable (fun z => L z • F (R z)) (cloud B) ∧
      (∫ z, F (f z) ∂cloud Q) = (∫ z, L z • F (R z) ∂cloud B) ∧
      ‖(∫ z, F (f z) ∂cloud Q) - ∫ z, F (j z) ∂cloud J‖ ≤ c * r^D * errorFare K D U x := by
  intro C B δ f j L R q r A
  obtain ⟨h1,h2⟩ := h.rawMoments hK q
  have hq : 2 * D ≤ q := by unfold q highMoment; omega
  refine ⟨h1.price hF hq, h2.price hF hq,?_⟩
  have H := h.onFull hK (hF.restored (b ∘ l) g)
  change
    Integrable (fun z => F (R (inUnits (b ∘ l) g (f z)))) (cloud Q) ∧
    Integrable (fun z => F (R (inUnits (b ∘ l) g (j z)))) (cloud J) ∧
    Integrable (fun z => L z • F (R z)) (cloud B) ∧
    (∫ z, F (R (inUnits (b ∘ l) g (f z))) ∂_) = (∫ z, L z • F (R z) ∂cloud B) ∧
    ‖(∫ z, F (R (inUnits (b ∘ l) g (f z))) ∂_) -
      ∫ z, F (R (inUnits (b ∘ l) g (j z))) ∂_‖ ≤ _ at H
  have he z : R (inUnits (b ∘ l) g z) = z := restore_inUnits _ (ne_of_gt h.g_pos) _
  simp_rw [he] at H
  exact H
end ReadPrice
end YM.PhysicalNext.PhysicalGuard7f546
