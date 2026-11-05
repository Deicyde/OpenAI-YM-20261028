import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Complex.Columns
import YM.Next.FREE_KERNELS.Lifts
import YM.SectorNext.VACUUM_NORMALIZATION.Round


/-!
# Finite Gaussian exponent bookkeeping in real color components

Correction S = AC-I (in this order); no symmetry of S. No contours
or analytic continuation of a measure. On regular coordinates only,
so e.g. X can include a constant row even when J is empty. Applications
also below on a completed Gram and on ordered spatial kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets
open MeasureTheory ProbabilityTheory Filter Matrix Function Lattice RG Precision SectorNext.Vacuum
open scoped Topology BigOperators MatrixOrder Classical
variable {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
abbrev Table (J : Type*) := Round.Wall J
abbrev Vec (J : Type*) := J → ℝ

theorem corrected_pos {A C : Table J} (ha : A.PosDef) (hc : C.IsHermitian) {q : ℝ}
    (h : Round.rowRate q (A*C-1)) (hq : q<1) : C.PosDef := by
  let M := CFC.sqrt A
  have hm : M*M=A := CFC.sqrt_mul_sqrt_self _ ha.posSemidef.nonneg
  have hs : star M=M := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hU : IsUnit M := isUnit_of_mul_isUnit_left (hm.symm ▸ ha.isUnit)
  let B := M*C*M
  have hB : B.IsHermitian := by
    change star (M*C*M)=M*C*M
    rw [star_mul,star_mul,hs,show star C=C from hc, Matrix.mul_assoc]
  apply hU.posDef_star_left_conjugate_iff.mp
  rw [hs]; exact hB.posDef_iff_eigenvalues_pos.mpr fun i => by
    let v : Vec J := ⇑(hB.eigenvectorBasis i)
    let y := M*ᵥv
    have hv : B*ᵥv=hB.eigenvalues i • v := hB.mulVec_eigenvectorBasis i
    have hh : (A*C-1)*ᵥy=(hB.eigenvalues i-1) • y := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, show (A*C)*ᵥy=(M*B)*ᵥv by
        unfold y B; rw [mulVec_mulVec,←hm]; simp only [Matrix.mul_assoc],← mulVec_mulVec,hv,
        Matrix.mulVec_smul, sub_smul,one_smul]
    have hy : 0<‖y‖ := by
      apply norm_pos_iff.mpr; intro H
      have hl := Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det _).mp hU)
      have hv : v=0 := by rw [← Matrix.one_mulVec v,← hl,← mulVec_mulVec,(show M *ᵥ v = 0 from H),Matrix.mulVec_zero]
      exact hB.eigenvectorBasis.orthonormal.ne_zero i (by ext k; exact congr_fun hv k)
    have hk := Round.rows_norm _ h y
    rw [hh,norm_smul,Real.norm_eq_abs] at hk
    have hr := abs_le.mp (le_of_mul_le_mul_right hk hy)
    linarith only [hr.1,hq]

abbrev quad {J : Type*} [Fintype J] (A : Table J) (x : Vec J) := dotProduct x (A*ᵥx)

def gram (D : Matrix X J ℝ) : Table J := D.transpose*D

def energy (D : Matrix X J ℝ) (b : Vec X) (a : Vec J) := dotProduct (D*ᵥa+b) (D*ᵥa+b)
/-- E eta, external source argument `b` here denotes F0 (thus
`Dᵀ *ᵥ b` is E b). -/
def drag (D : Matrix X J ℝ) (b : Vec X) (g : ℝ) (μ : Vec J) := (-g⁻¹) • (D.transpose*ᵥ(D*ᵥμ+b))

def cost (D : Matrix X J ℝ) (b : Vec X) (β : ℝ) (a : Vec J) := β * energy D b a / 2

def tilt (D : Matrix X J ℝ) (b : Vec X) (β g : ℝ) (C : Table J) (μ Z : Vec J) :=
  -cost D b β μ + dotProduct (drag D b g μ) Z + quad (C⁻¹-gram D) Z / 2

omit [DecidableEq J] in
lemma drag_eq (D : Matrix X J ℝ) (b : Vec X) (g : ℝ) (μ : Vec J) :
    drag D b g μ = (-g⁻¹) • (gram D *ᵥ μ + D.transpose *ᵥ b) := by
  rw [drag, gram, mulVec_add, mulVec_mulVec]

lemma untilt (D : Matrix X J ℝ) (b : Vec X) {β g : ℝ} (h : β*g^2=1) (C : Table J) (μ Z : Vec J) :
    quad C⁻¹ Z / 2 = cost D b β (μ + g • Z) + tilt D b β g C μ Z := by
  have hg : β*g = g⁻¹ := by
    have hh : g ≠ 0 := by rintro rfl; norm_num at h
    field_simp; linarith only [h]
  have he : dotProduct (D.transpose*ᵥ(D*ᵥμ+b)) Z = dotProduct (D*ᵥZ) (D*ᵥμ+b) := by
    rw [dotProduct_comm _ Z, Matrix.dotProduct_mulVec _ D.transpose, vecMul_transpose]
  unfold tilt cost energy drag gram quad
  rw [smul_dotProduct,he]
  simp only [Matrix.sub_mulVec,dotProduct_sub,← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ D.transpose,
    Matrix.vecMul_transpose, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,dotProduct_add,
    smul_dotProduct,dotProduct_smul,dotProduct_comm b (D*ᵥZ),dotProduct_comm (D*ᵥμ) (D*ᵥZ), smul_eq_mul]
  rw [← hg]
  nlinarith only [show β*g^2*dotProduct (D*ᵥZ) (D*ᵥZ)=1*dotProduct (D*ᵥZ) (D*ᵥZ) from congr_arg (· * dotProduct (D*ᵥZ) (D*ᵥZ)) h]

lemma covariance_log {A C : Table J} (ha : A.PosDef) (hc : C.IsHermitian) {q : ℝ}
    (h : Round.rowRate q (A*C-1)) (hh : 0≤q) (hq : q<1) :
    Real.log C.det = - Real.log A.det + Round.traceLog (A*C-1) := by
  obtain ⟨hC,_,_,he⟩ := Round.exact_trace ha hc _ rfl h hh hq
  rw [show 1+(A*C-1)=A*C by abel, Matrix.det_mul, Real.log_mul ha.det_pos.ne' hC.ne'] at he
  rw [he]; ring

/-- Same C as used in the exponent. Valid even if determined by other (held)
variables; not a claim that integrating those other variables gives a Gaussian. -/
abbrev law (C : Table J) := multivariateGaussian (0 : EuclideanSpace ℝ J) C



end YM.Further.CurvedGaussianJets
