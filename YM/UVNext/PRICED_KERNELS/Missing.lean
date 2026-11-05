import YM.UVNext.PRICED_KERNELS.Assembly


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
Only at degrees j=3,4 classical residuals, error on α and per-period
Born wave.

Test on a single chosen Forest/period and a single Choice there.

Doesn't test agreement in continuation strong enough to advance/stitch a
Trajectory.

Still need a nonlinear path generator (see LocalBuilder) with
coherent paths on all these kernels.

These estimates also are for the prices
previously chosen; any additional pre-L floors and post-L costs still need
to be included in the right order and if sizes/prices don't work with these
actual estimates must pivot or strengthen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Pressure Laurent Exterior Bloch Matrix Bid Tree
open Push.PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge}
section edge
variable {c f : Side} {S : StepData c f}

/-- On-shell scalar asked even per ONE forest and choice. No asking estimates
at an unobserved wave, and sign of α comparison inherited. Caller can choose
any such resolution (or prove for all at that tree), including tests with
i,j not opposite. No symmetry/parity assumed to drop this latter
requirement. -/
structure Expensive (X Z : PathData G) (p q : Clip) (α : ℝ) (A : ChartRatio G) (η Γ d Λ : ℝ)
    (U : Forest S.ratio) (t : S.Choices) : Prop where
  result : ∃ ρ, Critical U p X ρ ∧ PriceGap U p X η ∧
    (∀ j, 2 < j → j ≤ 4 → iteratedFDeriv ℝ j (fun x => tested U t p X x (ρ x)) 0 =
      iteratedFDeriv ℝ j (fun x => mainTerm q Z (represent x)) 0) ∧
    ∀ (i j : Site c) (σ τ : TypeFace 1 → G.ColorIndex → ℂ),
      (∀ x y, ‖σ x y‖≤1) → (∀ x y, ‖τ x y‖≤1) →
      let W := ![wave i σ,wave j τ]
      |iteratedFDeriv ℝ 2 (thermal U t p X ρ A) 0 W - iteratedFDeriv ℝ 2 (draft α Z q) 0 W| ≤
        (Fintype.card (Site c):ℝ)*Γ*Λ*Real.exp (-d*c.val)
end edge

section Calendar
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)} {M : Preparations P D}
  {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y} {a : Levels G}
  {V : Horizon a}
  (h : Permit M I a) (hv : Motor P a V) {Q : ℕ → ℕ → PathData G} (hi : Installed P a V Q)

/-- Leave peaks and kinetic errors at the actual arrays but only higher
orders. On `result`, we request the Expensive estimates on ANY one solution
they can find at that tree: they can obtain one by `ask_scene` and spend the
estimates (so are not asked to *solve* for it as an independent input).
Bookings on arbitrary other periods at same m consume same α, Q path. No
request of erasing harmonics. `Expensive` includes the gap info because
on_shell compares their p to the requested ρ; uniqueness needs a gap on
the chosen resolution. It follows from Installed/Permit, so take it here
by costing at known `M.gap`. -/
structure Remaining (V : Horizon a) (M : Preparations P D) (q : AfterBill)
    (Q : ℕ → ℕ → PathData G) (α : ℕ → ℕ → ℝ) : Prop where
  high N p j : 2 < j → j ≤ 4 → iteratedFDeriv ℝ j (fun x => mainTerm (a.params N).clip (Q N N) (represent (x:fieldDir G (a.S.side N p) 1))) 0 =
      iteratedFDeriv ℝ j (fun x => Wilson.energy (represent (x:fieldDir G (a.S.side N p) 1))) 0
  err N m : m < N → let j := a.clock.J (m+1); let i := a.clock.J m
                      |α N m + G.slopeConstant * Real.log (a.S.block m).val| ≤ P.slopePrices.kineticErr j i
  per N m : m < N → ∀ p, let S := a.clock.op m p
    let j := a.clock.J (m+1); let i := a.clock.J m
    let X := Q N (m+1); let Z := Q N m
    ∃ (F : Forest S.ratio) (k : S.Choices), Expensive X Z (a.params (m+1)).clip (a.params m).clip (α N m)
      (Next.Foundations.chart G) (M.gap j) (q.error j i) (q.decay j i) (a.clock.loopCap (m+1)) F k

-- V in Remaining just tracks the associated choice of horizon when referring to Q, α.
include h hi hv



end Calendar
end YM.UVNext.PricedKernels
