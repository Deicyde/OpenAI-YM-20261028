import YM.UVNext.COUPLING_RESET.Advance
import YM.UVNext.COUPLING_RESET.Normalized


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Actual prefix inputs to the reset calculation from the normalized integrals

Meant for use with a committed `bake.retain` guaranteeing Q has come from
the original Wilson measure via all the actual kernels. Not requiring that
the higher representation coefficients be given as functions off-trajectory
or that the matching has already produced the outgoing activities. Neither
the availability of those bake hypotheses nor the accuracy estimates on the
integrals and activities are unconditional. `crossings` gives a test in terms
of a primitive score-error estimate on the same Wilson/kernel expressions.
Away from endpoints in that score test the value evaluated need not lie on the
curve, so this method requires rather strong estimates when `s` is long.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.BetaTransport Lattice Wilson RG RG.Shoot RG.Supply Input Precision Set Function Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {a : Levels G} {s : Set ℝ} {b : BetaCurve} {N m p : ℕ}

structure Prefix (a : Levels G) {N m p : ℕ} (hm : m < N) (s : Set ℝ) (b : BetaCurve) (Q : In a m p) : Prop where
  beta : ∀ x∈s, (Q x).beta = b x (m+1)
  eval : ∀ x∈s, (Q x).eval = wilsonRead a p N b (m+1) hm x

variable {hm : m < N} {Q : In a m p} {x : ℝ}









variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {B : Directed G I Z K P} {q : ResetPrices}
    {V : Config G (B.a.S.side m p)} {F : Terms B.a m p}

section Crossing
variable {R : In B.a m p}




end Crossing


end YM.UVNext.CouplingReset
