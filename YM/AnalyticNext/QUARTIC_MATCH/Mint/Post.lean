import YM.AnalyticNext.QUARTIC_MATCH.Mint.Figures
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Savings


/-!
# The quantitative sequential remainder

Pre-Delays but post-L constant (contrast with pre-L recurrence). Also for arbitrary
exact matches within those budgets. Valid even for an inherited witness's Answer, as
*germs*. Full-berth statements use NECESSARILY a calibrated representative through
the berth; retain the stationary field of Answer/actual reps for everything taking
its germ (don't replace histories, assemblies etc.). Mounted uniform for all such inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Mint
open Filter Function Lattice Laurent Matrix RG RG.Supply Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Next Tree Joint BoxChain Mail Analyzers
open Progress.Joint Local Local.Budget Local.Wages Hessian Scheduling Affairs Radius
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

namespace Post
open Radius  Radius.Fetch Radius.Compiled
variable {G : Gauge}
section gears
variable {c f : Side} (S : StepData c f) (p q : Clip) (R T : PathData G) (H : Forest S.ratio)
variable {F W : Dir G c → ℝ}


/-- True Taylor bounds, not just coefficient ceilings. Standard value
estimate is `value` (includes actual volume). In `prices`, any anchor valuations
can be charged. See also `kernels`. For higher jets, exponent uses natural
subtraction; full path placement still applies. No waves required. Use with
the proofs of smoothness in `Pays` etc. -/
structure TaylorAt (f : Dir G c→ℝ) (r C t : ℝ) (k : ℕ) : Prop where
  room : 0<r
  pos : 0≤C
  rate : 0<t
  value x : ‖x‖ < r → |f x| ≤ C*Fintype.card (Site c)*‖x‖^ (5:ℕ)
  uniform {x : Dir G c} {j : ℕ} : ‖x‖<r → j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ C * Fintype.card (Site c) * ‖x‖^(5-j)
  prices {x : Dir G c} {j : ℕ} : ‖x‖<r → j≤k → ∀ (d : Fin j→Dir G c) (b : Fin j→Site c→ℝ),
      (∀ i, Polish.Menu (Fetch.trials G t i) d (fun u=> b u i)) → |iteratedFDeriv ℝ j f x d| ≤ C * ‖x‖^(5-j) * ∑ i : Site c,∏ j,b j i
  kernels {x : Dir G c} {j : ℕ} : ‖x‖<r → j ≤ k → ∀ (d : Fin j→Body 1 c) (b : Fin j→G.Color) (i : Fin j),
      let s := Compiled.strip t j
      (∏ k, Green.wt s (d k).1 (d i).1) * |iteratedFDeriv ℝ j f x (fun k=> Compiled.stick (d k) (b k))| ≤
        C*Premium.overall s * ‖x‖^(5-j) * ∏ k, ‖b k‖




end gears

section schedule
variable {K : MapPrices} {s : Survey G} {q : Quote} {P : Printed 2} {R : Printed 3} {U : Counters G K s.B.kernel P R} {v : ℕ→ ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D} {V : Delays Θ} {Y : Bar V} {I : Wait Y}
    {a : Levels G} {H : Horizon a} {B : Beam K D} {e : ℕ→ ℕ→ Exchange}
    {p : ℕ→ ℕ→ Postage} {m N : ℕ}











end schedule
end Post
end YM.AnalyticNext.QuarticMatch.Mint
