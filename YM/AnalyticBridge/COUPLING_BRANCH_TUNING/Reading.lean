import YM.AnalyticBridge.COUPLING_BRANCH_TUNING.Activity
import YM.Next.SCHEDULE.Post
import YM.Push.COMMON_WITNESSES.Link
import YM.UVNext.COUPLING_RESET.Regular

set_option warningAsError false

/-!
# Rather than price the error in absolute cumulant units

Use early template income (eq:HRGv setting, as in `COUPLING_RESET.Regular`) on just ACTUAL
parameter comparisons, with additional drift estimates on its labels. This removes the
`Signal.error` requirement on straight comparisons of entire Wilson/kernel paths between two
histories. The inverse dial can work just with the resulting *endpoint* error. No Taylor or trial
probes in U are implicit in this currency: it uses the positive exact evals on two physical all-good
coarse fields, one flat, with kinetic and loop and pre-R BEFORE reset; keeps normalization and
masks; no K-log estimated. Combine with drift estimates on the final activity template AT FIXED
dial (not fixed outgoing beta) in the next module. `Curve` and the canonical data at this B change
only as authorized by COUPLING_RESET.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.BranchTuning

open Lattice Wilson RG Shoot RG.Supply Input Precision UVNext.CouplingReset
open scoped Matrix.Norms.Frobenius BigOperators Topology

variable {G : Gauge} {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {B : Directed G I Z K P} {a : Levels G} {N m p : ℕ}
    {q : ResetPrices} {η : ℕ → ℝ}

/-- Per-level unnormalized currencies (uniform in period and call depth). Target-regime buys
regular variations through `order` (can be less than budget order) and forced value variations. Two
separate meters for motion in x (units: actual incoming β change) and in the test dial (additive
correction relative to predictor using that actual β and our `Kin`). The held currencies will be
redeemed in units of actual β change on the held level, not top parameter. This is a *strong*
Lipschitz regime for actual labels; E does not promise these costs. Doesn't include buying any of
the missing physical inputs named by these rates. -/
structure Rates where
  order : ℕ → ℕ
  /-- per-anchor early comparison price -/
  early : ℕ → ℝ
  /-- per-anchor post comparison price at fixed correction -/
  outE : ℕ → ℝ
  /-- per-hit post comparison price at fixed correction -/
  outK : ℕ → ℝ
  dialE : ℕ → ℝ
  dialK : ℕ → ℝ
  keepE : ℕ → ℝ
  keepK : ℕ → ℝ
  /-- allowed distortion per step -/
  loss : ℕ → ℝ

/-- An economic certificate not a receipt for actual costs. Does not buy `CubicGate` in
`Prereset` or the actual Catalog/remainder estimates. No additive loss of exponent fed from loss in
β; these comparisons use the SAME level budgets as starting with PricedReset. -/
structure Licensed (a : Levels G) (η : ℕ → ℝ) (q : ResetPrices) (r : Rates) : Prop where
  reset : PricedReset a η q
  order_le m : r.order m ≤ (a.budget m).order
  early_nonneg m : 0 ≤ r.early m
  outE_nonneg m : 0 ≤ r.outE m
  outK_nonneg m : 0 ≤ r.outK m
  dialE_nonneg m : 0 ≤ r.dialE m
  dialK_nonneg m : 0 ≤ r.dialK m
  keepE_nonneg m : 0 ≤ r.keepE m
  keepK_nonneg m : 0 ≤ r.keepK m
  loss_nonneg m : 0 ≤ r.loss m
  loss_le m : r.loss m ≤ 1/4
  beat m : 2*(2*r.early m + r.outE m) ≤ r.loss m * (η (a.clock.J m) * (a.budget m).threshold^2)
  vertical m : r.dialE m ≤ funds a m q
  keep_regular m : r.outE m + r.dialE m * r.loss m ≤ (1-r.loss m)*r.keepE m
  keep_forced m : r.outK m + r.dialK m * r.loss m ≤ (1-r.loss m)*r.keepK m

variable {r : Rates}





open Set
variable {s : Set ℝ} {u : ℝ → ℝ} {Q : In B.a m p} {S : ℝ → Activities G (B.a.S.side m p)}
    {V : Config G (B.a.S.side m p)} {R : Rates}

/-- Prices only additional zeroth-order variation of the PRE-reset regular labels at every anchor
(and the fixed dictionaries); for correction via the probe secant this suffices. -/
structure BeforeReading (B : Directed G I Z K P) (q : ResetPrices) (r : Rates) (N m p : ℕ) (s : Set ℝ)
    (Q : In B.a m p) (u : ℝ → ℝ) (S : ℝ → Activities G (B.a.S.side m p)) : Prop where
  pre : Prereset B q s N m p Q u S
  meters : ∀ x ∈ s, ∀ y ∈ s,
    RegularDrift (B.a.budget m) 0 (S y) (S x) (r.early m * |(Q y).beta-(Q x).beta|)











/-- Physical supplier cut for the strong Lipschitz regime. Additional (particularly E, K)
comparisons are estimated on actual two-variable templates *before* finding the dial root. Could
ignore the dial in F for E's direct prescription. Keep strictly separate from constructing
Prereset (which requires estimates on the actual integrated sectors), labels with Catalog's full
controlled and continuous representation at these exponents (hard selectors, all positions, path
lengths), and Remainder giving full field evaluator identity at roots. The latter physical work is
required even for a merely continuous family. NONE of these receipts supplied as physical proofs
here. Handoff from each call (e.g. obtaining Remainder.shape even on true sums with winding), their
pricing dependencies and the absence of derivative-order loss all remain extra hypotheses. Even at
order=0 one still needs full k E estimates from e.g. the complementary transfer work. -/
structure Candidates (B : Directed G I Z K P) (η : ℕ → ℝ) (q : ResetPrices) (r : Rates) (s : Set ℝ) (N m p : ℕ)
    (Q : In B.a m p) (V : Config G (B.a.S.side m p)) (F : Terms B.a m p) : Prop where
  usable : Usable B η N m p V
  catalog : Catalog (board B N F) s (window B.a m q) (B.a.clock.allowance m) (B.a.clock.forcedAllowance m)
  remainder : Remainder B N m p q s Q V F
  emits : ∃ u S, BeforeReading B q r N m p s Q u S
  horiz : ∀ x∈s, ∀ y∈s, ∀ d∈ window B.a m q, let Δ := (Q y).beta-(Q x).beta
    Slew (B.a.budget m) (r.order m) (F y d) (F x d) (r.outE m*|Δ|) (r.outK m*|Δ|)
  vert : ∀ x∈s, ∀ b∈window B.a m q, ∀ d∈window B.a m q,
    Slew (B.a.budget m) (r.order m) (F x d) (F x b) (r.dialE m*|d-b|) (r.dialK m*|d-b|)

variable {F : Terms B.a m p}





end YM.AnalyticBridge.BranchTuning
