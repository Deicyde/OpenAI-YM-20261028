import YM.Next.SCHEDULE.Continuing
import YM.Push.PRICE_COMPILER.Flows
import YM.UVNext.PRICED_KERNELS.Seats



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Residual inputs on one Permit

Use `Wired`, `Ways`/Canonical bills before solving path recursion. Expose
ONLY nonlinear atom estimates/choices on these actual objects, including
compatibility with whatever additional choices (if any) the full path generator needs.
No requests for proof of row budgets nor linear or scene or Teller costs. If using
another pre-schedule basis can also use these adapters locally wherever `Paid` meets
the issued Before. `KineticRemainder` is a separate input if pursuing α.
Don't conclude the required continuation predicates here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Pressure Laurent Exterior Bloch
open Push.PriceCompiler Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

/-- Actual nonlinear atom part of PathInputs. Keep loop jet signs and
invariance using PathData's own definitions, hence on the same labels.
Not asking l¹ without true path lengths. This module supplies the independent
linear (row) budget and attached normalizations. -/
structure Atoms (σ two three four : ℝ) (Q : PathData G) : Prop where
  loop : SumBudget (fun i => (Q.loop i).budget σ) two
  cubic : SumBudget (fun i => (Q.cubic i).budget σ) three
  quartic : SumBudget (fun i => (Q.quartic i).budget σ) four
  invariant i : (Q.loop i).Invariant ∧ (Q.cubic i).Invariant ∧ (Q.quartic i).Invariant
  jets : Q.loop_jets

lemma Billed.merge {P : Before} {a : Levels G} {V : Horizon a} {N m : ℕ} {Q : PathData G}
    (h : Billed P a V N m Q) {two three four C : ℝ}
    (hw : Atoms (a.params m).width two three four Q)
    (he : P.amount.born (a.clock.J m) ≤ C ∨
      ∃ j, StepStages j (a.clock.J m) ∧ P.amount.sends j (a.clock.J m) ≤ C) :
    Normalized Q (a.params m).clip ∧ PathMass Q (a.params m).width C two three four := by
  obtain he | ⟨j,hj,he⟩ := he
  · have hx := h.top
    have hv := (a.params m).width_pos
    have hp := receipt_le hx (show (a.params m).width ≤ _ by linarith only [hv]) he
    exact ⟨⟨hw.invariant,h.metric,hw.jets⟩, hv,hp,hw.loop,hw.cubic,hw.quartic⟩
  have hx := h.edge j hj
  have hv := (a.params m).width_pos
  have hp := receipt_le hx (show (a.params m).width ≤ _ by linarith only [hv]) he
  exact ⟨⟨hw.invariant,h.metric,hw.jets⟩,hv,hp,hw.loop,hw.cubic,hw.quartic⟩

def StartAtoms (P : Before) (a : Levels G) (N : ℕ) (Q : PathData G) :=
    let j := a.clock.J N; let v := a.params N; let C := P.amount.born j
    2*v.width ≤ P.opening.born j → Atoms v.width 0 C C Q

def NextAtoms (P : Before) (a : Levels G) (m : ℕ) (R Q : PathData G) :=
    let L : ℝ := (a.S.block m).val; let j := a.clock.J (m+1); let i := a.clock.J m
    let v := a.params m
    let C := classicalCost (P.amount.sends j i) L (a.params (m+1)).paths
    let t := P.slopePrices
    2*v.width ≤ P.opening.transfers j i →
    t.inputStrip j i / L ≤ (a.params (m+1)).width / 2 →
    Budgeted a (m+1) R → Atoms v.width (t.cost j i L (a.clock.loopCap (m+1))) C C Q





section Permit
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
  {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
  {a : Levels G} (h : Permit M I a) {V : Horizon a} (hv : Motor P a V)

/-- Keep the *same V* for every ask. Includes also SCHEDULE version to work at narrower
rates and larger ceilings if needed, WITHOUT taking later costs to price this
calendar. This part uses `Scheduling.narrower`. Also offers moments on the actual
row at working width, no dropping labels. -/
structure Installed (P : Before) (a : Levels G) (V : Horizon a) (Q : ℕ → ℕ → PathData G) : Prop where
  prices : PathInputs P a Q
  linear N m : m ≤ N → Billed P a V N m (Q N m)
  uses N m : m ≤ N → let i := a.params m
    ∀ σ C w : ℝ, 0 < σ → σ ≤ i.width → i.paths ≤ C → a.clock.loopCap m ≤ w →
      (Q N m).Bounds i.clip σ C w

include h in
lemma install {Q : ℕ → ℕ → PathData G} (h₁ : PathInputs P a Q)
    (ha : ∀ N m,m ≤ N → Billed P a V N m (Q N m)) : Installed P a V Q :=
    ⟨h₁,ha,fun N m hm _ _ _ hp hw hc hW => Next.Scheduling.narrower
      (h.budgets h₁ N m hm) hp hw hc hW⟩

lemma Installed.budget {Q : ℕ → ℕ → PathData G} (ha : Installed P a V Q) {N m : ℕ} (hi : m ≤ N) :
    Budgeted a m (Q N m) := ha.uses N m hi _ _ _ (a.params m).width_pos le_rfl le_rfl le_rfl

include h hv




/-- Recursive use. Ask `StartAtoms`/`NextAtoms` only of these generators, not a path
history. Caller can produce a different admissible tie convention every time,
including adversarially within *true cover* limits at the negotiated layout
prices. Require proving the generator actually outputs those row choices!(One
such spelling costs for all roots, via charge_layout.) That leaves nonlinear
estimates and whatever compatibility required with OTHER bounds as red gates.
`Ready`, `Keeps` for e.g. additional relations; not licenses to generate paths.
The solution sequence glues both, no picking independent per-period continuation
witnesses.
-/
def Allowed (H : Bed) (g : LayoutPrices) (i : ℕ) (Q : PathData G) :=
    Q.row = Canonical.row H ∨ ∃ p : Ways (g.stride i) (g.base i) (g.mass i), Q.row = p.row H



structure LocalBuilder (P : Before) {a : Levels G} (g : LayoutPrices) (V : Horizon a)
    (Ready : ℕ → ℕ → PathData G → Prop) (keeps : ℕ → ℕ → PathData G → PathData G → Prop) : Prop where
  cutoff N : ∃ Q, StartAtoms P a N Q ∧ Allowed (V.H N N) g (a.clock.J N) Q ∧ Ready N N Q
  step N m : m < N → ∀ R, Ready N (m+1) R → Billed P a V N (m+1) R → Budgeted a (m+1) R →
    ∃ Q, NextAtoms P a m R Q ∧ Allowed (V.H N m) g (a.clock.J m) Q ∧ Ready N m Q ∧ keeps N m R Q


end Permit
end YM.UVNext.PricedKernels
