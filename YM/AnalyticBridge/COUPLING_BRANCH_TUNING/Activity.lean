import Mathlib
import YM.Next.BOUNDARY.Coordinates
import YM.Next.SCHEDULE.Blocks
import YM.Next.UV_STRESS.Across
import YM.Push.PRICE_COMPILER.Post

set_option warningAsError false

/-!
# Per-anchor (resp. per-hit) receipts for parameter variations, 

Parameter comparisons BEFORE summing.

Use actual supports, thresholds and orders in use.

No
validity/vanishing/log assumption on those early terms here.

Do not take a derivative of an
indicator!

For propagated Lipschitz bounds one might want *fewer* variation derivatives than in
normal validity and `Curve` (danger of spending an order in reparameterizing integral terms);
still charge the requested P.mass.

E itself does NOT supply Lipschitz variation by its continuity
clause; obtaining receipts at these costs on upcoming curves is a separate producer obligation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.BranchTuning

open Lattice Wilson RG Shoot 
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff

variable {n : Side} {G : Gauge} {P : BudgetPoint}

/-- Same regular dictionary, prices at each anchor (including path and flag footprints as
charged in the production hypotheses). `r` will be ≤ P.order when using. -/
structure RegularDrift (P : BudgetPoint) (r : ℕ) (F H : Activities G n) (v : ℝ) : Prop where
  eq_reg : F.reg = H.reg
  receipt : ∃ b : ℕ → ℝ,
    (∀ i, 0 ≤ b i ∧ ∀ U, Healthy P.threshold (F.reg i).support U →
      ∀ l, List.length l ≤ r → (∀ A∈l, P.dirBound (F.reg i).site A) →
        ‖leftDerivs (F.E i) l U - leftDerivs (H.E i) l U‖ ≤ b i) ∧
    ∀ o : Site n,
      SumBudget (fun i => if (F.reg i).site = o then P.mass (F.reg i).support (b i) else 0) v

/-- Same forced dictionary (predicates, flags including dead data); estimates at all U,
without any smoothness in U for those tests/payloads. -/
structure ForcedDrift (P : BudgetPoint) (F H : Activities G n) (w : ℝ) : Prop where
  eq_forced : F.forced = H.forced
  receipt : ∃ b : ℕ → ℝ, (∀ i, 0 ≤ b i ∧ ∀ U, ‖F.K i U-H.K i U‖ ≤ b i) ∧
    ∀ o : Site n,
      SumBudget (fun i => if o ∈ (F.forced i).support then P.mass (F.forced i).support (b i) else 0) w

/-- Full (through requested `r`) Lipschitz regime's two costs on the address list. -/
structure Slew (P : BudgetPoint) (r : ℕ) (F H : Activities G n) (v w : ℝ) : Prop where
  regular : RegularDrift P r F H v
  forced : ForcedDrift P F H w

variable {F H Q : Activities G n} {v w v' w' q u δ : ℝ} {r r' : ℕ}

















/-! Prices originally per anchor/hit, can include infinite address sums. The passage to absolute
total summability pays the WHOLE torus (#sites); in particular no such factor allowed when
transmitting budgets down the calendar. For contrast this total is appropriate; density is
relative to the full Haar and the gain will also be extensive. -/











end YM.AnalyticBridge.BranchTuning
