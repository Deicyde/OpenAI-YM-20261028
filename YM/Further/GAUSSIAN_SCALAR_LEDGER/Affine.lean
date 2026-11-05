import YM.Further.GAUSSIAN_SCALAR_LEDGER.Gaussian


set_option warningAsError false

/-!
# Extracting **affine** Gram rows

These are the regular scalar/link-color variables, frozen columns
already moved to `b0`. Over ℝ with counting dotProduct. All channel
fees (and orientations) must be in the arguments; here we neither
construct the stationary estimates nor fix the caller's rows. Use on
the real tilted chart only. See  ff. Not a replacement of
the measure of the remainder by an unbounded approximation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function MeasureTheory
open scoped BigOperators Topology

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ]

/-- `ρ` includes channel & color coordinates of the selected rows. -/
def precision (D : Matrix ρ ι ℝ) : Wall ι := Dᵀ * D

def linearCost (D : Matrix ρ ι ℝ) (b0 : VV ρ) := Dᵀ *ᵥ b0

def sizeSq (D : Matrix ρ ι ℝ) (b0 : VV ρ) (a : VV ι) : ℝ :=
  (D *ᵥ a + b0) ⬝ᵥ (D *ᵥ a + b0)

omit [Fintype ι] in
lemma hermitian_precision (D : Matrix ρ ι ℝ) : (precision D).IsHermitian := by
  simp [precision, Matrix.IsHermitian]

lemma dot_cross {σ : Type*} [Fintype σ] (D : Matrix σ ι ℝ) (x : VV ι) (y : VV σ) :
    (D *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Dᵀ *ᵥ y) := by rw [dotProduct_mulVec _ Dᵀ,vecMul_transpose]

lemma move_expands (D : Matrix ρ ι ℝ) (b0 : VV ρ) (μ z : VV ι) (g : ℝ) :
    sizeSq D b0 (μ + g • z) = sizeSq D b0 μ +
      2 * g * (z ⬝ᵥ (precision D *ᵥ μ + linearCost D b0)) +
      g ^ 2 * (z ⬝ᵥ (precision D *ᵥ z)) := by
  let y := D *ᵥ μ + b0
  unfold sizeSq
  rw [show D *ᵥ (μ + g • z) + b0 = y + g • (D *ᵥ z) by
      rw [mulVec_add,mulVec_smul]; unfold y; abel]
  change (y + _) ⬝ᵥ (y + _) = y ⬝ᵥ y + _ + _
  rw [add_dotProduct,dotProduct_add y y (g • _),dotProduct_add (g • _) y (g • _), dotProduct_comm y (g • _),
      smul_dotProduct, smul_dotProduct, dotProduct_smul]
  unfold y linearCost precision
  simp only [smul_eq_mul]
  rw [dot_cross D, mulVec_add, mulVec_mulVec, dot_cross D, mulVec_mulVec]; ring

def stroke (D : Matrix ρ ι ℝ) (b0 : VV ρ) (μ : VV ι) (g : ℝ) :=
  -g⁻¹ • (precision D *ᵥ μ + linearCost D b0)

variable [DecidableEq ι]

def frco (D : Matrix ρ ι ℝ) (C : Wall ι) (b0 : VV ρ) (μ : VV ι) (g : ℝ) (z : VV ι) :=
  -sizeSq D b0 μ / (2*g^2) + stroke D b0 μ g ⬝ᵥ z + (z ⬝ᵥ ((C⁻¹-precision D) *ᵥ z))/2

def charge (D : Matrix ρ ι ℝ) (b0 : VV ρ) (g : ℝ) (a : VV ι) :=
  sizeSq D b0 a / (2*g^2)

lemma frco_eq (D : Matrix ρ ι ℝ) (b0 : VV ρ) {C : Wall ι} (hC : C.PosDef)
    (μ z : VV ι) {g : ℝ} (hg : 0 < g) :
    modeCost C * (lawPDF C z * Real.exp (frco D C b0 μ g z)) =
      Real.exp (-charge D b0 g (μ + g • z)) := by
  have he : -(z ⬝ᵥ (C⁻¹ *ᵥ z)) / 2 + frco D C b0 μ g z =
      -charge D b0 g (μ+g • z) := by
    rw [frco,charge, stroke, smul_dotProduct, dotProduct_comm _ z,
      sub_mulVec, dotProduct_sub, move_expands, smul_eq_mul]; field_simp; ring
  unfold lawPDF
  rw [mul_assoc (modeCost C)⁻¹,mul_inv_cancel_left₀ (modeCost_pos hC).ne', ← Real.exp_add, he]

def sample (D : Matrix ρ ι ℝ) (C : Wall ι) (b0 : VV ρ) (μ : VV ι) (g : ℝ)
    (ψ : VV ι → ℝ) (z : VV ι) :=
  Real.exp (frco D C b0 μ g z) * ψ (μ + g • z)

/-- `ψ` includes true masks and all other terms. Don't need to assume it
would be integrable with another Gaussian or off-real contour. -/
theorem charge_integral (D : Matrix ρ ι ℝ) (b0 : VV ρ) {C : Wall ι} (hC : C.PosDef)
    (μ : VV ι) (g : ℝ) (hg : 0 < g) (ψ : VV ι → ℝ)
    (hi : Integrable (fun a => Real.exp (-charge D b0 g a) * ψ a)) :
    Integrable (sample D C b0 μ g ψ) (fieldLaw C) ∧
    (∫ a, Real.exp (-charge D b0 g a) * ψ a) =
      (2*Real.pi*g^2)^((Fintype.card ι : ℝ)/2) * Real.sqrt C.det *
        ∫ z, sample D C b0 μ g ψ z ∂fieldLaw C := by
  obtain ⟨hz,h⟩ := moves g hg μ hi
  let f := sample D C b0 μ g ψ
  have he : (fun z => Real.exp (-charge D b0 g (μ+g • z)) * ψ (μ+g • z)) =
      (fun z => modeCost C * (lawPDF C z * f z)) := by
    funext z; rw [← frco_eq _ _ hC _ _ hg]; simp only [f,sample,mul_assoc]
  change Integrable (fun z => Real.exp (-charge D b0 g (μ+g • z)) * ψ (μ+g • z)) _ at hz
  rw [he] at hz
  refine ⟨(integrable_law hC f).mpr ((integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (modeCost_pos hC).ne') _).mp hz),?_⟩
  calc
    _ = g ^ Fintype.card ι * ∫ z, Real.exp (-charge D b0 g (μ+g • z)) * ψ (μ+g • z) := h
    _ = g ^ Fintype.card ι * modeCost C * ∫ z, lawPDF C z * f z := by
          rw [he,integral_const_mul, mul_assoc]
    _ = _ := by rw [← integral_law hC f,modeCost_scale _ hg]

section schur





variable [DecidableEq ρ]







end schur

end YM.Further.GaussianScalar
