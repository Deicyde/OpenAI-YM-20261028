import YM.Push.PRICE_COMPILER.Compiler
import YM.Push.PRICE_COMPILER.PathBudget


/-!
# Kernel & path-facing consumer (conditional)

This file exposes examples of exact sufficient hypotheses on the actual path
presentations, and uses them downstream. `PathInputs` could be produced on the
same Levels after every prescribed additional floor/delay. They are local raw
transfer ESTIMATES of amounts (shape of E `r34cap`,`b2loop`) and exact kernel
algebra obligations. They are **NOT** known. Use of the hypotheses pays the
costs through *every step*, not assuming the Amount or theta Cap handoffs have
worked. Nor does it ignore arbitrary within-index history. At the use have a
`Permit`: no assumptions about Directed or a realized vacuum.

`KineticRemainder` below is for a further optional consumer (includes full
matching assumptions not needed for Teller price use).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG RG.Supply Wilson Precision Pressure Bid Tree Exterior Bloch
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace

variable {G : Gauge}

def Budgeted (a : Levels G) (m : ℕ) (R : PathData G) :=
    let b := a.params m
    R.Bounds b.clip b.width b.paths (a.clock.loopCap m)

/-- Shape of a physical transfer cost estimate. Only when *input*
already bounded. The buy signal includes an input width test of the form
numerator/L ≤ σ/2 (compare ); widths needed on the returned
estimates are committed once and for all. No bad per-use erosion, also
when `j=i`. A margin `2σ_out ≤ pre-L offered rate` is given for proving
the output bounds. Return a bound at the committed `σ_out` (not asked
for the higher-width estimate after the proof).

Should prove estimates e.g., by induction from top; may be an implication
at each application under additional numerical gates that one has bought and
shown. This statement does not purchase them. Keep actual path labels; cone
price uses both normalization and actual exponential LENGTH mass. -/
structure TransferPrices (P : Before) (a : Levels G) (m : ℕ) (R U : PathData G) : Prop where
  provides :
    let L := (a.S.block m).val
    let j := a.clock.J (m+1)
    let i := a.clock.J m
    let b := a.params m
    let C := classicalCost (P.amount.sends j i) L (a.params (m+1)).paths
    let v := P.slopePrices
    2*b.width ≤ P.opening.transfers j i →
    v.inputStrip j i / L ≤ (a.params (m+1)).width / 2 →
    Budgeted a (m+1) R →
      Normalized U b.clip ∧
      PathMass U b.width C (v.cost j i L (a.clock.loopCap (m+1))) C C

/-- For each cutoff and all steps on the issued calendar. Actual weighted
row/canonical estimates with all normalizations & counting still required;
not `Kin.Planned`. Note quote `sends` must include the pre-L row estimates as
well, not just the cubic/quartic coefficients. -/
structure PathInputs (P : Before) (a : Levels G) (R : ℕ → ℕ → PathData G) : Prop where
  top (N : ℕ) :
    let j := a.clock.J N
    let b := a.params N
    let C := P.amount.born j
    2*b.width ≤ P.opening.born j → Normalized (R N N) b.clip ∧ PathMass (R N N) b.width C 0 C C
  steps N m : m < N → TransferPrices P a m (R N (m+1)) (R N m)

namespace Permit
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
    {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Permit M I a)
include h

theorem transfer {m : ℕ} {R U : PathData G} (hu : TransferPrices P a m R U) (hR : Budgeted a (m+1) R) :
    Budgeted a m U := by
  let j := a.clock.J (m+1); let i := a.clock.J m
  let L := (a.S.block m).val
  have he : StepStages j i := step_paid a m
  have hb := h.pre.at_edge h.paid m
  obtain ⟨hn,hp⟩ := hu.provides (by rw [params_eq h.paid]; exact P.opening.transfers_ge he)
    (by rw [params_eq h.paid]; exact hb.phase) hR
  let q := a.params m
  let b := a.params (m+1)
  have hw : classicalCost (P.amount.sends j i) L b.paths ≤ q.paths := by
    unfold b q; rw [params_eq h.paid, params_eq h.paid]; exact hb.cap
  have hg := hp.mono q.width_pos le_rfl hw (h.loopCost m) hw hw
  exact hg.bounds hn le_rfl le_rfl le_rfl

theorem budgets {R : ℕ → ℕ → PathData G} (g : PathInputs P a R) (N m : ℕ) (hm : m ≤ N) : Budgeted a m (R N m) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    obtain ⟨hs,hp⟩ := g.top N (by rw [params_eq h.paid]; exact P.opening.born_ge _)
    have he : P.amount.born (a.clock.J N) ≤ (a.params N).paths := by
      rw [params_eq h.paid]; exact P.amount.born_le _
    have hx := hp.mono (a.params N).width_pos le_rfl he ((show (0:ℝ) ≤ 2 by norm_num).trans (cap_ge a N)) he he
    exact hx.bounds hs le_rfl le_rfl le_rfl
  | of_succ k hk H => exact h.transfer (g.steps N k hk) H



/-- Spend the stationary price on *actual* `Budgeted` (e.g., any input
above after `budgets`). Require Horizon estimates and compatible
read A,A0,T and Sworn etc. Can't assert a uniformly analytic radius from
this, or anything stronger than the Scene χ at this price. -/
theorem called {V : Horizon a} (ha : V.Suffices (P.frozen G))
    {R : PathData G} (N m p : ℕ) (hg : m < N) (F : Forest (a.clock.op m p).ratio)
    (hR : Budgeted a (m+1) R) (hx : Attached (V.H N (m+1)) R) (ho : Sworn (V.H N (m+1)) (a.S.side (m+1) p) G) :
      let S := a.clock.op m p
      let b := (a.params (m+1)).clip
      let j := a.clock.J (m+1)
      PriceGap F b R (M.gap j) ∧ ∃ ρ, Critical F b R ρ ∧
        Guessed F (installed S.ratio (V.towers N m).A0) ρ ∧ HeatG F b R ρ (V.H N m) :=
  M.scenes.asks _ _ _ (a.clock.op m p) h.paid.kernel (block_eq h.paid m) rfl (h.larger m p) F
    _ _ _ _ R _ _ _ _ _ _ (V.towers N m) (ha.crossings N m p hg) (ha.all N (m+1) hg _) hR
    hx ho (ha.all N m hg.le _)
omit h in
/-- The Tube obtained from the actual path & towers. -/
def tube (V : Horizon a) (R : ℕ → ℕ → PathData G) (N m p : ℕ) : Tube G (a.clock.op m p) :=
    ⟨V.towers N m,R N (m+1), (a.params (m+1)).clip,R N m,(a.params m).clip⟩

/-- Purchases even with no known loop identification or Directed. -/
theorem tickets {R : ℕ → ℕ → PathData G} (hx : PathInputs P a R)
    {V : Horizon a} (ha : V.Suffices (P.frozen G))
    (hr : ∀ N m, m ≤ N → Attached (V.H N m) (R N m)) (N m p : ℕ) (hc : m<N) :
    let j := a.clock.J (m+1); let i := a.clock.J m
    let S := a.clock.op m p; let Q := tube V R N m p
    Teller.Funds (Testing.query (P.sheet G f) (P.frozen G) j i) S Q ∧
      ∀ (A : Stores S) (U : Config G _) (k : S.Choices) (X : Config G _) (F : Forest S.ratio),
        Stores.SliceSet S F U → Stores.Plot A U k X (a.clock.hatBeta m) (M.w j i) →
          M.rate j * (a.clock.threshold (m+1))^2 * A.shares ≤ A.assessed Q (a.clock.hatBeta m) U (S.prediction U k) X := by
  intro j i S Q
  let q := Testing.query (P.sheet G f) (P.frozen G) j i
  have hi : (a.params m) = q.below := congr_fun h.paid.stage i
  have hj : (a.params (m+1)) = q.top := congr_fun h.paid.stage j
  have hy : Teller.Funds q S Q := by
    refine ⟨h.paid.kernel, rfl, (P.sheet G f).has _, ha.costs N m hc,
      congr_arg Stage.clip hi, congr_arg Stage.clip hj, ?_, ?_⟩
    · obtain he := h.budgets hx N m hc.le
      obtain hh := h.budgets hx N (m+1) hc
      rw [← hi, ← hj]; exact ⟨_,_,hh,he⟩
    exact ⟨_,_,hr _ _ hc,hr _ _ hc.le,ha.stack N m p hc⟩
  exact ⟨hy,M.charges.ticket h.post.entry h.paid m p Q hy⟩
end Permit

/-- Residual physical input for the `kinetic` consumer. Include actual
sign conventions and full period matching. The estimates of PathInputs
*don't* imply any of these. For this cut they are asked just on given
Levels; a producer will have to find conditions for which they can be
met over all required Rolls (set `kernel` etc. floors at pre-L service and
post-L bar demands). Here if using existing Scene choice callable for all F,
it suffices to supply matches for the resulting critical solutions. We don't
postulate any relationship with a different theta/history.
-/
structure KineticRemainder {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)} {a : Levels G} (V : Horizon a)
    (M : Preparations P D) (q : AfterBill) (R : ℕ → ℕ → PathData G) (α : ℕ → ℕ → ℝ) : Prop where
  peak N p j : j ≤ 4 → SameJet j (fun x => mainTerm (a.params N).clip (R N N) (represent (x:fieldDir G (a.S.side N p) 1)))
      (fun x => Wilson.energy (represent x))
  err N m : m < N → let j := a.clock.J (m+1); let i := a.clock.J m
                       |α N m + G.slopeConstant * Real.log (a.S.block m).val| ≤ P.slopePrices.kineticErr j i
  response N m : m < N → ∀ (p : ℕ) (F : Forest (a.clock.op m p).ratio),
    let Y := R N (m+1); let X := R N m
    let S := a.clock.op m p
    let u := (a.params (m+1)).clip; let v := (a.params m).clip
    let j := a.clock.J (m+1); let i := a.clock.J m
    PriceGap F u Y (M.gap j) → ∀ ρ, Critical F u Y ρ → Guessed F (installed S.ratio (V.towers N m).A0) ρ → HeatG F u Y ρ (V.H N m) →
      ClassicalMatch F u v Y X ρ ∧ FiniteBound F Y X u v (α N m) (Next.Foundations.chart G) ρ
        (q.error j i) (q.decay j i) (a.clock.loopCap (m+1))


end YM.Push.PriceCompiler
