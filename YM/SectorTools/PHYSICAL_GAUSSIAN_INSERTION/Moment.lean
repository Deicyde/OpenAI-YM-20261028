import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Escape

/-!
# Exact exponentially tilted quadratics and the likelihood moment threshold

Strict definiteness of `mixed` necessary and sufficient. The exact moment
comparison retains the determinant and the affine completion (including the
sign in the posterior mean). No `integral_undef` values used as numbers for a
nonintegrable price. In particular the test handles arbitrary real `p > 1`
and singular precision AT the moment threshold.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianInsertion

open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment (Relative.trade)
open scoped Topology BigOperators Classical ENNReal

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {A C D : Gaussian.Table ι} {a d h : Vec ι} {p : ℝ}

/-- Precision tested on the *whole* physical counting coordinate space. `p`
is the power on the likelihood of the target `(A, a)`. -/
def mixed (A D : Gaussian.Table ι) (p : ℝ) := p • A⁻¹ + (1 - p) • D⁻¹

lemma mixed_symm (hA : A.PosDef) (hD : D.PosDef) : (mixed A D p).IsSymm :=
  ((isHermitian_iff_isSymm.mp hA.inv.isHermitian).smul _).add
    ((isHermitian_iff_isSymm.mp hD.inv.isHermitian).smul _)

def bias (A : Gaussian.Table ι) (p : ℝ) (h : Vec ι) := p • (A⁻¹ *ᵥ h)

/-- Posterior mean (if the power test passes) is `d - offset` in the
original coordinates, `-offset` in reference-centered coordinates. -/
def offset (A D : Gaussian.Table ι) (p : ℝ) (h : Vec ι) := (mixed A D p)⁻¹ *ᵥ bias A p h

/-- The p-th moment itself, not raised to `1/p`. Only a price under strict
coercivity. h = reference center - target center. Thus in particular the
affine shift term in the exponent is computed AFTER fixing the actual two centers.
-/
def moment (A D : Gaussian.Table ι) (p : ℝ) (h : Vec ι) : ℝ :=
  (Real.sqrt D.det / Real.sqrt A.det)^p *
    (Real.sqrt (mixed A D p)⁻¹.det / Real.sqrt D.det) *
    Real.exp ((offset A D p h ⬝ᵥ bias A p h - p * force A h) / 2)

lemma moment_pos (hA : A.PosDef) (hD : D.PosDef) (hm : (mixed A D p).PosDef) :
    0 < moment A D p h :=
  mul_pos (mul_pos
    (Real.rpow_pos_of_pos (div_pos (Real.sqrt_pos.mpr hD.det_pos)
      (Real.sqrt_pos.mpr hA.det_pos)) p)
    (div_pos (Real.sqrt_pos.mpr hm.inv.det_pos) (Real.sqrt_pos.mpr hD.det_pos)))
    (Real.exp_pos _)

lemma offset_solves (hm : (mixed A D p).PosDef) :
    mixed A D p *ᵥ offset A D p h = bias A p h := by
  unfold offset
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hm.det_pos.ne'), one_mulVec]

private lemma shape (hA : A.PosDef) (z : Vec ι) :
    p * force A (h+z) + (1-p) * force D z =
      quad (mixed A D p) z + 2 * (z ⬝ᵥ bias A p h) + p * force A h := by
  rw [add_comm h z]
  change p * quad A⁻¹ (z+h) + (1-p) * quad D⁻¹ z = _ + p * quad A⁻¹ h
  rw [quad_add (isHermitian_iff_isSymm.mp hA.inv.isHermitian), bias, dotProduct_smul]
  unfold quad mixed
  rw [add_mulVec, dotProduct_add, smul_mulVec, smul_mulVec,
    dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

lemma completed (hA : A.PosDef) (hm : (mixed A D p).PosDef) (z : Vec ι) :
    p * force A (h+z) + (1-p) * force D z =
      force (mixed A D p)⁻¹ (offset A D p h + z) -
        offset A D p h ⬝ᵥ bias A p h + p * force A h := by
  rw [shape hA, add_comm (offset A D p h) z]
  let Q := mixed A D p
  let u := offset A D p h
  change _ = quad Q⁻¹⁻¹ (z+u) - _ + _
  rw [nonsing_inv_nonsing_inv _ (IsUnit.mk0 _ hm.det_pos.ne'),
    quad_add (isHermitian_iff_isSymm.mp hm.isHermitian),
    show Q *ᵥ u = _ from offset_solves hm,
    show quad Q u = offset A D p h ⬝ᵥ bias A p h by unfold quad Q u; rw [offset_solves hm]]
  ring

lemma likelihood_rpow (hA : A.PosDef) (hD : D.PosDef)
    (hm : (mixed A D p).PosDef) (x : Vec ι) :
    likelihood A D a d x ^ p = moment A D p (d-a) *
      likelihood (mixed A D p)⁻¹ D (d-offset A D p (d-a)) d x := by
  let b := bias A p (d-a)
  let u := offset A D p (d-a)
  let I := (mixed A D p)⁻¹
  let R := (Real.sqrt D.det / Real.sqrt A.det)^p
  let L := Real.sqrt I.det / Real.sqrt D.det
  let L' := Real.sqrt D.det / Real.sqrt I.det
  let y := x-d
  let P := (u ⬝ᵥ b - p * force A (d-a))/2
  let S := (force D y - force I (u+y))/2
  unfold likelihood Relative.trade
  rw [Real.mul_rpow (by have := hD.det_pos; positivity) (Real.exp_pos _).le,
    ← Real.exp_mul, show d-(d-u)=u by abel]
  change R * Real.exp _ = R*L*Real.exp P*(L'*Real.exp S)
  have he : L * L' = 1 := by
    unfold L L'
    have ht := Real.sqrt_pos.mpr hD.det_pos
    have hu : 0 < Real.sqrt I.det := Real.sqrt_pos.mpr hm.inv.det_pos
    field_simp
  rw [show R*L*Real.exp P*(L'*Real.exp S)=R*(L*L')*(Real.exp P*Real.exp S) by ring,
    he, mul_one, ← Real.exp_add]
  have hh := completed (h:=d-a) hA hm y
  unfold S I P u b y
  unfold y at hh
  congr 2
  linarith only [hh]

section Posterior

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- If retaining more than the moment: insert a function into the exact
p-power integral (use with CompleteSpace for Bochner expectation). -/
lemma posterior (hA : A.PosDef) (hD : D.PosDef) (hm : (mixed A D p).PosDef)
    (a d : Vec ι) (f : Vec ι → X) :
    let μ := law (mixed A D p)⁻¹ (d-offset A D p (d-a))
    (Integrable (fun x => (likelihood A D a d x)^p • f x) (law D d) ↔ Integrable f μ) ∧
    (∫ x, (likelihood A D a d x)^p • f x ∂law D d) = moment A D p (d-a) • ∫ x, f x ∂μ := by
  intro μ
  let u := d-offset A D p (d-a)
  let m := moment A D p (d-a)
  let F := fun x => likelihood (mixed A D p)⁻¹ D u d x • f x
  have he : (fun x => (likelihood A D a d x)^p • f x) = m • F := by
    funext x
    rw [likelihood_rpow hA hD hm]
    exact (smul_smul ..).symm
  have hp : 0 < m := moment_pos hA hD hm
  obtain ⟨hu,hf⟩ := affine_change hm.inv hD u d f
  constructor
  · rw [he, integrable_smul_iff hp.ne']
    exact hu.symm
  change (∫ x, (fun x => (likelihood A D a d x)^p • f x) x ∂law D d) = _
  rw [he]
  change (∫ x, m • F x ∂law D d) = m • ∫ x, f x ∂law (mixed A D p)⁻¹ u
  rw [integral_smul, hf]

end Posterior

/-- Finite case of the exact Lp integral. -/
theorem power_integral (hA : A.PosDef) (hD : D.PosDef) (hm : (mixed A D p).PosDef) (a d : Vec ι) :
    Integrable (fun x => likelihood A D a d x ^ p) (law D d) ∧
      (∫ x, likelihood A D a d x ^ p ∂law D d) = moment A D p (d-a) := by
  obtain ⟨hi,he⟩ := posterior hA hD hm a d fun _ => (1 : ℝ)
  exact ⟨by simpa using hi.mpr (integrable_const _), by simpa using he⟩

private lemma power_necessary (hA : A.PosDef) (hD : D.PosDef)
    (h : Integrable (fun x => likelihood A D a d x ^ p) (law D d)) : (mixed A D p).PosDef := by
  let u := d-a
  rw [integrable_law, cloud_formula hD, integrable_withDensity_iff_integrable_smul'
    (measurable_ratio D |>.ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  let M := (coat D)⁻¹ * (Real.sqrt D.det / Real.sqrt A.det)^p
  have hM : 0 < M := mul_pos (inv_pos.mpr (coat_pos hD))
    (Real.rpow_pos_of_pos (div_pos (Real.sqrt_pos.mpr hD.det_pos)
      (Real.sqrt_pos.mpr hA.det_pos)) p)
  let c := -(p * force A u / 2)
  have he (z : Vec ι) : (ENNReal.ofReal (ratio D z)).toReal • likelihood A D a d (d+z)^p =
      M * Real.exp (-quad (mixed A D p) z/2 - z ⬝ᵥ bias A p u + c) := by
    have hh := shape (D:=D) (p:=p) (h:=u) hA z
    rw [ENNReal.toReal_ofReal (ratio_pos hD z).le]
    unfold likelihood Relative.trade ratio
    rw [add_sub_cancel_left, Real.mul_rpow
      (by have := hD.det_pos; positivity) (Real.exp_pos _).le, smul_eq_mul,
      mul_mul_mul_comm, ← Real.exp_mul, ← Real.exp_add]
    change M * _ = M * _
    unfold c u
    unfold u at hh
    exact congr_arg _ (congr_arg Real.exp (by linarith only [hh]))
  simp_rw [he] at h
  rw [integrable_const_mul_iff (IsUnit.mk0 M hM.ne')] at h
  exact posDef_of_integrable_quadratic _ (mixed_symm hA hD) _ _ h

/-- Includes failure at the semidefinite boundary, ALL centers. -/
theorem power_iff (hA : A.PosDef) (hD : D.PosDef) :
    Integrable (fun x => likelihood A D a d x ^ p) (law D d) ↔ (mixed A D p).PosDef :=
  ⟨power_necessary hA hD, fun h => (power_integral hA hD h a d).1⟩













variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {q : ℝ} {F : Vec ι → X}





end YM.SectorTools.PhysicalGaussianInsertion
