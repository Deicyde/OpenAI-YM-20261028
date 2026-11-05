import YM.Further.CURVED_GAUSSIAN_JETS.Schur
/-!
# Which flat curvature covariance? Finite generalized Schur accounting

Derive a conditional identity **without** assuming invertibility of a free
ungauged link precision, a Fourier formula on nonzero momenta, or a
limit dropping harmonic modes. Instead, intrinsic curl bill from a
positive definite curvature metric. The (only) inverse needed in the
conditional part is on the named slice, not the ambient potential. Our
hypotheses specify how to handle residual constraints; e.g. paying a
gap alone on a subspace that discards some actual curvatures would be
invalid. The pseudo-inverse is just a means of choosing coordinates for
the calculation. No interpretation of the free cutoff answer as a kernel
of interacting fields, nor using that inverse as the truncated window C.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Fiber
open Function Filter MeasureTheory Set Matrix Unitary Lattice Precision
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {I X U J Y : Type*} [Fintype I] [Fintype X] [Fintype U] [Fintype J] [Fintype Y]
    [DecidableEq I] [DecidableEq X] [DecidableEq U] [DecidableEq J] [DecidableEq Y]





def strength (D : Matrix X I ℝ) (H : Table X) := D.transpose*H*D










def principal (d : Matrix X U ℝ) (H : Table X) (q : Matrix J U ℝ) (k : ℝ) := strength d H+k • (q.transpose*q)

variable (d : Matrix X U ℝ) (f : Matrix X I ℝ) (c : Matrix Y J ℝ) (H : Table X) (H' : Table Y)
    (q : Matrix J U ℝ) (k : ℝ) (T : Matrix U J ℝ) (l : Matrix X Y ℝ)
/-- Tree stationary identities desired, on any handed-off real linear
slice (not identities of untested replacement kinetic equations). -/
structure Bare : Prop where
  stiffness : strength d H*T=q.transpose*strength c H'
  noise : q*T=1-k⁻¹ • strength c H'

namespace Bare
variable {T d c H H' q k}
lemma chart (h : Bare d c H H' q k T) (hk : k≠0) : principal d H q k*T = k • q.transpose := by
  simp only [principal,Matrix.add_mul,Matrix.smul_mul,Matrix.mul_assoc q.transpose,h.stiffness,h.noise,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul,smul_sub,
     smul_smul, mul_inv_cancel₀ hk,one_smul,add_sub_cancel]
lemma home (h : Bare d c H H' q k T) (hk : k≠0) (hd : (principal d H q k).PosDef) :
    Schur.home (principal d H q k) (k • q.transpose) = T := by
  rw [Schur.home,←chart h hk,← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd.det_pos.ne'),Matrix.one_mul]
lemma marginal (h : Bare d c H H' q k T) (hk : k≠0) (hd : (principal d H q k).PosDef) (B : Table J) :
    Schur.schur (principal d H q k) (k • q.transpose) (B+k • 1)=B + strength c H' := by
  rw [Schur.schur,Matrix.transpose_smul, Matrix.transpose_transpose,Matrix.mul_assoc _ _ (k • q.transpose),←Schur.home,h.home hk hd, Matrix.smul_mul,h.noise,smul_sub,smul_smul,mul_inv_cancel₀ hk,one_smul]; abel
end Bare


end YM.Further.CurvedGaussianJets.Fiber
