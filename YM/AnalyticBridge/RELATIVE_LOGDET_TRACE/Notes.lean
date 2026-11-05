import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Resolvent
import YM.Next.FOUNDATIONS.SU2
import YM.Next.FREE_KERNELS.Signal
import YM.Push.FREE_RESOLVENT.ListJets

/-!
# Log variation, including through `1+S` (NOT necessarily symmetric)

Qualitative Jacobi formula. No Taylor comparison through moving flags
licensed by this. Sign checked on each real directional step. Includes
also tag responses on straight A homotopies (for completed keys, no
assumption of shared block sizes). Use of ordinary real log near any
invertible in this auxiliary calculation does not permit replacing actual
matrix PosDef hypotheses at the main ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Set Function Filter Matrix MeasureTheory FreeResolvent TestD 
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E→Square ι} {x : E} {k : ℕ}

namespace Notation
omit [Fintype ι] [DecidableEq ι] in
private lemma missing (i : ι) (e : ι ≃ ι) (he : e≠Equiv.refl ι) : ∃ j : ι, j ≠ i ∧ e j≠ j := by
  contrapose! he
  ext j
  by_cases hv : j=i
  · subst j; by_contra hh
    exact (hh (show e i=i from (e.injective (he (e i) hh))))
  exact he j hv



omit [DecidableEq ι] in
def traceL (ι : Type) [Fintype ι] : Square ι →L[ℝ] ℝ := ∑ i, TestD.evaluate i i
omit [DecidableEq ι] in
lemma traceL_apply (M : Square ι) : traceL ι M=M.trace := by unfold traceL; rw [_root_.sum_apply]; rfl













def marks (P Q : Square ι) (t : ℝ) := P+t • Q



end Notation
end YM.AnalyticBridge.RelativeLogdet
