import YM.Push.PRICE_COMPILER.Authors

/-!
# Continuity versus funding (`Curve`, )

If the ONLY loss in some proposed step lemma is the exponent for
fixed-period continuity, that's not necessarily a cumulative cost
obstruction: recover it for free in B70's `Curve`, with the same fixed
threshold/directions and common witness. Even `B` in the comparison can
change JUST for this purpose. Key: the support currency d_B (NOT true path
length) is bounded at each fixed volume.

Absolutely don't do that for the quantitative estimates across periods.
Show also in Lean why the analogous *uniform* expenditure is unavailable.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG Wilson RG.Supply Pressure Corona RG.Shoot
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-- Same local test, not the same expenditure. -/
structure SameTest (P Q : BudgetPoint) : Prop where
  orders : P.order = Q.order
  powers : P.power = Q.power
  thresholds : P.threshold = Q.threshold

lemma SameTest.symm {P Q : BudgetPoint} (h : SameTest P Q) : SameTest Q P :=
  ⟨h.orders.symm,h.powers.symm,h.thresholds.symm⟩

















end YM.Push.PriceCompiler
