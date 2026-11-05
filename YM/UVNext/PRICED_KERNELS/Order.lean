import YM.Push.PRICE_COMPILER.Canonical
import YM.UVNext.PRICED_KERNELS.Bridge



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Buying Before tables that the physical free kernels will honor

In particular direct can actually be capped with a strict positive payment
(INCLUDING harmonic case) and launch orders nonempty, and there is room subsequently
e.g. to honor the price compiler's path-facing numerical requests plus actual canonical
row quotes on the retained repaired horizons.

Issue ANY compatible tables before
considering L, and include b floors of Free in a request together with the unseen other
additional L asks (not using L!).

Obtain joint existence **retaining** those free
kernels across Permit consumers.

Same-stage edges included.

Nonlinear work must still price estimates
IN THIS ORDER, not just observe some prices work at a first L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Pressure
open Push.PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

/-- Keep ceilings on direct; never increase linear tail price (but may have
to lower it to remain legal). Provisional relaxation left alone. This use of
clips has a strictly positive per-index lower bound for each coefficient
(Clip fields), NOT a uniform-in-j one. Include a strict gap below 1 for possible
later E hypotheses (and harmonic safety); and if Catalog.fit inflates? at
stages ≥4 the producer itself had better ensure at most 1, but don't rely on
reversal of its bound. Clips can equivalently be proposed separately *after*
seeing Catalog with a certificate meeting the direct terms, see `issue`.
-/
def cap (p : Clip) (γ : ℝ) (h : 0 < γ) : Clip where
  direct := min (min p.direct (1/2)) γ
  linear := min p.linear (min (min p.direct (1/2)) γ / 32)
  relaxation := p.relaxation
  quadratic_pos := lt_min (lt_min p.quadratic_pos (by norm_num)) h
  tail_pos := lt_min p.tail_pos (div_pos (lt_min (lt_min p.quadratic_pos (by norm_num)) h) (by norm_num))
  kink := lt_of_le_of_lt (min_le_right ..) (by
    have hx : 0 < min (min p.direct (1/2)) γ := lt_min (lt_min p.quadratic_pos (by norm_num)) h
    linarith)
  radius_pos := p.radius_pos



/-- Replace the three clip and kernel-facing parts of provisional numerical inputs
while keeping κ/order/first unchanged. Construct actual-compatible canonical path
width and row quotes (costed on `preMap`, not X), and allow the caller to supply
actual other Opening, Amounts, LoopPrices etc numbers at the stipulated order.
Their own feasibility/compatibility not asserted. `late` below receives
installed LoopPrices too, to allow e.g. a relaxation need to depend on those
pre-L quotes. (Can instead assemble externally if wanting a different but
still pre-L DAG.) No function in these arguments receives actual L or any
post-L reports. Orders/first at least should already reflect any needed
budgets. We don't care here whether caps/amount are monotone externally since
the price compiler internally uses active common rates and pay envelopes.
-/
structure EndNumbers where
  relaxation : ℕ → ℝ
  reserve : HaloBill
  lead : ℕ → ℝ
  columns : ℕ → ℝ

structure Charges where
  wants : (ℕ → Clip) → FlatBill → MapPrices → Openings
  asks : (ℕ → Clip) → FlatBill → MapPrices → Openings → Amounts -- choose for installed Openings including width change
  loops : (ℕ → Clip) → FlatBill → MapPrices → Openings → Amounts → LoopPrices
  late : (ℕ → Clip) → FlatBill → MapPrices → Openings → Amounts → LoopPrices → EndNumbers



def issue (G : Gauge) (p : Before) (Q : FlatBill)
    (c : ℕ → Clip) (R : Charges) : Before :=
  let K := preMap (p.kernelChoice G) c Q G
  let w := Canonical.orderWidth K (R.wants c Q K)
  let a := Canonical.orderRows K (R.asks c Q K w)
  let o := R.loops c Q K w a
  let f := R.late c Q K w a o
  { p with
    clip := c, flat := Q, opening := w, amount := a,
    slopePrices := o,relaxation:=f.relaxation,reserve:=f.reserve,lead:=f.lead,columns:=f.columns }



lemma linear_paths (G : Gauge) (p : Before) (Q : FlatBill) (c : ℕ → Clip) (R : Charges) :
    let P := issue G p Q c R
    let K := preMap (p.kernelChoice G) c Q G
    let w := R.wants c Q K
    let a := R.asks c Q K P.opening
    Canonical.Quotes (P.frozen G) P.opening P.amount ∧ P.opening.wish ≤ w.wish ∧
      a.born ≤ P.amount.born ∧ a.sends ≤ P.amount.sends := by
  intro P K w a
  obtain ⟨ht,hs,hq⟩ := Canonical.orderRows_quotes K w a
  exact ⟨hq,Canonical.orderWidth_le K w,ht,hs⟩

/-- A stock of Direct choices after knowing γ (no need to rewrite linear if
already planning it on the actual smaller direct). -/
structure Caps (first : ℕ) (γ : ℕ → ℝ) where
  clips : ℕ → Clip
  meets i : first ≤ i → (clips i).direct ≤ γ i



section Issuance
variable (P : Before) (X : MapPrices) (l : ℕ → ℝ)

/-- End-to-end quantitative schedules here, a reusable interface for *augmenting*
the various floors/delays at these orders. Also read local consumers/single
`wire` lemma to add to any other scheduling cuts if proving `Permit` there.
No universal or even on-this-schedule nonlinear estimates yet.
-/
structure Built (G : Gauge) (P : Before) (X : MapPrices) (l : ℕ → ℝ) (g : ℕ → ℕ) : Prop where
  pre : Before.Funded P G g
  nonempty : Nonempty (Rolls (P.sheet G g))
  post (D : Rolls (P.sheet G g)) (w : ℕ → ℕ → ℝ) (η : ℕ → ℝ) : (∀ i, 0 < η i) →
      ∃ M : Preparations P D, w ≤ M.w ∧ M.gap ≤ η ∧
        ∀ (q : AfterBill) (s : PostCost D → ℕ → ℝ), (∀ i, 0 < s (M.budget q) i) →
        ∃ T : Protection D, T.theta ≤ s (M.budget q) ∧ ∀ V : Delays T,
          ∃ W : Delays T, OrderedDelays W ∧ DelayLe V W ∧ ∀ U : Delays T, DelayLe W U →
            M.Ledger U ∧ ∀ β : ℝ, ∃ Y : Bar U, β ≤ Y.value ∧ Nonempty (Wait Y) ∧
              ∀ I : Wait Y, ∃ a : Levels G, Permit M I a
  receives {D : Rolls (P.sheet G g)} {M : Preparations P D} {T : Protection D} {W : Delays T}
    {Y : Bar W} {I : Wait Y} {a : Levels G} : Permit M I a → ∃ B V : Horizon a, Wired P a X l B V





end Issuance
end YM.UVNext.PricedKernels
