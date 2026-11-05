import YM.AnalyticBridge.COUPLING_BRANCH_TUNING.Reading
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.UV_STRESS.Union
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.SECTOR_MEASURE.Payment


set_option warningAsError false

/-!
# A normalized Lipschitz regime that fits the existing price machine NUMERICALLY

order of choices.

For stronger variation tracking one issue is whether
distortion allowance admits purchases even on a Run with unboundedly many within-stage
comparisons, or would require undoing kernel-price choices to accommodate e.g. torus
volume.

Offer one regime, uniform in N,p and same-stage repeats.

Held variation is per
unit actual β change, of order the label allowance divided by the hatted beta.

Must prove such
inputs with actual parameter and kernel/loop work before these prices are usable.

Doesn't
assume they're bought, just proves the **price** comparisons in `Licensed` can be
funded with these orders and explicit prequotes, joining PricedKernels on ONE clock.

If aiming for stronger exponents or weaker actual estimates must recheck gates (may
not hold).

Monitor references here held fixed, not varying across trials.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.BranchTuning
open Lattice RG RG.Supply Precision UVNext.CouplingReset Filter
open scoped BigOperators Topology ContDiff

variable {G : Gauge}

/-- Orders/cost multipliers fixed by stages. Choose with enough slack for the provider, ahead of
rolls when physical estimates require that. License arithmetic could issue even after rolls, but at
latest before delays. -/
structure Quote where
  order : ℕ → ℕ
  early : ℕ → ℕ → ℝ
  regular : ℕ → ℝ
  forced : ℕ → ℝ
  adjust : ℕ → ℕ → ℝ -- extra K cost for tuning dial
  early_pos j i : 0 < early j i
  regular_ge i : 1 ≤ regular i
  forced_ge i : 1 ≤ forced i
  adjust_pos j i : 0 < adjust j i

def eBasis (a : Levels G) (m : ℕ) : ℝ := a.clock.allowance m / a.clock.hatBeta m
def forceBasis (a : Levels G) (m : ℕ) : ℝ := a.clock.forcedAllowance m / a.clock.hatBeta m

/-- Quotes compiled on ACTUAL calendar, with no choice dependence on actual tuning endpoints,
β, depth, B.Kin etc. Need comparison inputs with same directions/order in play. -/
def staging (p : Quote) (q : ResetPrices) (a : Levels G) : Rates where
  order m := min (p.order (a.clock.J m)) (a.budget m).order
  early m := p.early (a.clock.J (m+1)) (a.clock.J m)* eBasis a m
  outE m := p.regular (a.clock.J m)* eBasis a m
  outK m := p.forced (a.clock.J m)* forceBasis a m
  dialE m := funds a m q
  dialK m := p.adjust (a.clock.J (m+1)) (a.clock.J m)*a.clock.forcedAllowance m
  keepE m := 4*(p.regular (a.clock.J m)* eBasis a m)
  keepK m := 4*(p.forced (a.clock.J m)* forceBasis a m)
  loss m := a.clock.allowance m/4

structure FitsValues (p : Quote) (q : ResetPrices) (η : ℕ → ℝ) (j i : ℕ) (x : ℝ) : Prop where
  signal : 8*(2*p.early j i+p.regular i) ≤ η i * (Push.PriceCompiler.mon x)^2
  regular : q.cost j i ≤ x^((1:ℝ)/10)
  forced : p.adjust j i ≤ x^((1:ℝ)/10)





open Push.PriceCompiler
variable {a : Levels G} {q : ResetPrices} {p : Quote} {η : ℕ → ℝ}





variable {S : Sheet G} {D : Rolls S} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}






variable {P : Before} {g : ℕ → ℕ} {X : MapPrices} {l : ℕ → ℝ}


end YM.AnalyticBridge.BranchTuning
