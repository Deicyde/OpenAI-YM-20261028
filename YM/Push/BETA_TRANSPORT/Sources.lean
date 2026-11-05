import YM.Push.BETA_TRANSPORT.History


/-!
# β variations through one common Family.path and its source pushes

In particular at the represented value of the parameter(s), assuming Selected
or Makes as appropriate, identify the above finite integrals with the actual
evaluations/normalized source densities, as functions, not merely after a
last integration. The derivatives here vary the β's *in the Wilson
weight and in all kernels*, for data held fixed otherwise (the labels, section,
reference transfer & terminal coordinates, thresholds etc are NOT being reselected).
Away from the attained β these new integrals still make sense, but need not be
represented by the same recipe. At no point vary separated tests or the extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open MeasureTheory Wilson Lattice RG Source Filter Set Gibbs
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {G : Gauge} (s : Levels G) (p N : ℕ) (b : ℕ → ℝ) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X]

def normalizedVacuum (m : ℕ) (hm : m ≤ N) := propagate s p N b (fun _ => (1:ℝ)) m hm










variable (C : Family G)

end YM.Push.BetaTransport
