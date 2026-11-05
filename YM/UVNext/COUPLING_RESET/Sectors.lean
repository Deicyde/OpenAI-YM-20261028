import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.SECTOR_MEASURE.Presented
import YM.UVNext.COUPLING_RESET.Prices
import YM.UVNext.COUPLING_RESET.Reset



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Optional sufficient estimates on the unmarked sector outputs

Test the two required values in the same exact normalized-kernel sector
operation. Keep a common log-normalization `v` (EXTENSIVE estimate, e.g.
from Gaussian/normalization analysis) in predicted term and in both core &
tail prices. Tail uses the true `leftOver`, core still uses interacting
integrals and needs *two-sided* bounds; absolute outer charges are NOT an
income of this form by themselves. No assertion of existence of such a split
(e.g., taking only one good record as core and adding all bad-sector prices
may well be insufficient in arbitrarily large volume; use other domain
hypotheses like `Income.pos`/`.surplus` if using more internal resummation).
Do not drop portions or replace an Allocation by summing raw plots. No
thermodynamic or relative-error cap on the representations uniformly over V
here. This is just to earn the scalar surplus, and not the `Catalog`, dial
and `Remainder` supplies, retained-sector predicates or next-call economics.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.SectorMeasure Push.SectorMeasure.Presented Push.PriceCompiler Filter Lattice RG RG.Supply Pressure Pressure.Stores
open Input Tree Wilson Precision
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n f : Side} {S : StepData n f} {x W κ u e : ℝ} {d : Allocation G S x W}
    {A : Forest S.ratio} {T : Tube G S} {Q : Rep G f} {V : Config G n}

/-- Scale e/2 in the exponent for the two core bounds, leaving a
relative-to-lower-bound reserve for tails. A stronger-than-necessary (real,
signed sums allowed) value test, possibly splitting differently at the two
probes. e scales like OUT-volume times the pre-reset allowance/4. No
independence or derivative-through-boundary assumptions. -/
def Split (d : Allocation G S x W) (A : Forest S.ratio) (T : Tube G S) (κ : ℝ) (Q : Rep G f) (V : Config G n) (u e : ℝ) :=
  ∃ C : Finset (Stores S),
    (∑ a ∈ C, cutEntry d A T Q a V) ∈ Set.Icc (Real.exp (u-e/2)) (Real.exp (u+e/2)) ∧
    (∑ a ∈ Finset.univ \ C, earn S G x κ Q.beta a.shares * leftOver d A T Q a V) ≤
      Real.exp (u-e/2)*(1-Real.exp (-e/2))



variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {L : Delays Θ} {Y : Bar L} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P) {q : ResetPrices} {N m p i j : ℕ}




end YM.UVNext.CouplingReset
