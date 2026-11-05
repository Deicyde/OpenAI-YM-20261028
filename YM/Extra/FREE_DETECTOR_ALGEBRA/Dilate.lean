import YM.Extra.FREE_DETECTOR_ALGEBRA.Filtrate

set_option warningAsError false

/-! Engineering scaling in Wick entries (including mixing lengths).
Deduced from power of off-origin kernel, nothing imposed at the
Wilson/ref coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Set Filter Tensor Analysis Maxwell Wick  Labels MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {G : Gauge} {n j : ℕ}

/-- Positive and negative factors; multiply the symbol of curvature order
j by `t^(j+2)`. -/
def scaleP (t : ℝ) : WickPol G →ₐ[ℂ] WickPol G := MvPolynomial.aeval fun i => ((t:ℂ)^costKey i) • MvPolynomial.X i

@[simp] lemma scale_X (t : ℝ) (i : Slot G) : scaleP t (MvPolynomial.X i) = ((t:ℂ)^costKey i) • MvPolynomial.X i := aeval_X ..



def Exact (p : WickPol G) (j : ℕ) := IsWeightedHomogeneous costKey p j








end YM.Extra.FD
