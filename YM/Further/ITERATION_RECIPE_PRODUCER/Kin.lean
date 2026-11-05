import YM.Further.ITERATION_RECIPE_PRODUCER.Crown

set_option warningAsError false

/-!
# Conditional production of a no-loss Kin with fixed UV boundary conditions

Heating and `extend` on consecutive actual levels, NEVER shrinking the
working widths as a function of (perhaps very large) depth in a stage; uses
the `ITERATION_NO_LOSS` arbitrary-depth receipts and the Joint-calendar gap.
Record all stations. Keep the constructor in an Exists (not Prop→kinetic data
from different callers); use the same witness in recipes.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe
open Filter Function Lattice Wilson RG RG.Supply Precision Bid Pressure Exterior Tree Extra.Iteration Next.Scheduling
open Progress.Joint WilsonStartup
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {s : Survey G} {K : MapPrices} {l : ℕ → ℝ} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
  {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y} {B : Beam K D} {u : ℕ → ℕ → Postage}
  {a : Levels G} {M : Horizon a} (ha : Paid I a) (hm : Panel K s.X l M)
  {U : Apertures} {A : ClassicalCosts} {H : QuantumCosts} (hp : Before (s.paper q v) U (request s A) H K)
  (hw : Warm H W) (hR : Heating M K U (request s A) H (B.price u) s.B.chart)

include ha hm hp hw hR


structure Engine {G : Gauge} {s : Survey G} {K : MapPrices} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
    {a : Levels G} {M : Horizon a} (U : Apertures) (A : ClassicalCosts) (B : Beam K D) (u : ℕ → ℕ → Postage)
    (k : Kin M s.B.chart) : Prop where
  top n : k.path n n = crown G (a.params n).clip
  worksheet : k.Planned (B.price u)
  tickets N m : m ≤ N → Ticket M K U A N m (k.path N m)
  stations N m : m < N → OnShell M (B.price u) N m (k.path N (m+1)) (k.stationary N m)


end YM.Further.IterationRecipe
