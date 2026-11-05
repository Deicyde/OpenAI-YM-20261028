import YM.Further.CURVED_GAUSSIAN_JETS.Algebra

/-!
# Finite Schur accounting (real, physical Hessian convention)

This version uses the *conditional fine precision* as pivot; does NOT
invert the other bare precision. After supplying an external coarse mass
one can obtain all block inverse identities. In its absence those would
not generally make sense in our application (even if there is a true
stationary branch).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Schur
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Precision 
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Table I) (Z : Matrix I J ℝ) (B : Table J)


def schur := B-Z.transpose*A⁻¹*Z
def home := A⁻¹*Z











end YM.Further.CurvedGaussianJets.Schur
