import YM.SectorNext.LARGE_FIELD_REMAINDERS.Absorb
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Leases


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Grants for the TRUE outgoing charge and represented density

`before`: pre-L issuer relative only to main teller query. `after`: also use
with a purchased W,κ (i.e., price earlier with any other post-L needs, then
only commit to Period/Roll scene if delay paid). Include explicit per-site
bills even though the intended application estimates per-whole-integral
post grant. Proofs with standard clipped base conventions in this library:

* `PaidHere.single`: actual tagged outgoing, clipped (`Mode.clipped`) or also
  with cut output factor (`Mode.shielded`). Book ANY integrable multiplier
  certified on the real k sector of U with the specified *per grant* valuations.
  Doesn't require sign. Includes arbitrary H b^n log loss besides K if first
  paid, also suitable for spans of local support prices. Do not set e.g.
  K=1 for unverified multipliers. `sheet_charge`, `output_charge` etc read
  this WHICH way required.
* `PaidHere.full`: all real fine representation terms at once, uniform in
  true path and label dictionary size and any compatible realization (tags
  not rerolled anywhere). Either leave the output cut factor out (can state
  the bill times `sieve` thereafter as well) or include it. In particular
  `Use.left`: actual `leftOver` multiplied by the charge's `earn`, with κ/2
  reserved, pre-Gaussian; can multiply by support and other charges whose log
  priced $H b^n(1+\\log y)$ per seed without losing that κ/2. Or just H=0.
  Note this is an estimate *following portionCost* even at the clipping kinks,
  not reconstructing columns holomorphically or after optional removal of
  prerequisites. `R.scalar` remains, unconstrained by Lawful; estimate is
  genuinely volume-uniform relative to just that named scalar of the input (with
  VolPrice paid), or the specified β-scaled per-site volume bill. Never inferring
  a scalar bound on the remainders from `Envelope` alone.

No comparisons being made to claimed RG first-system Mayer bounds here. In
particular, at the MUCH more expensive determinant scale, expect per-volume
C_L^vol in these bounds; `Mode.shielded` expenditure then useful at fluctuation
link scale but V cut factor is not available to callers requiring it to survive
explicitly. These grants do not close the RG step. Proof doesn't require stationary
path hypotheses beyond the typed Funds, Fits, Lawful etc.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Metric Oriented Presented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {G : Gauge} (P : Teller G) (L : Side) (W κ σ B H : ℝ) (n : ℕ)

/-- threshold and physical use at coarse-HAT x, separate from PointCharge. -/
structure Use (C γ : ℝ) (D : Mode → ℝ) (x : ℝ) : Prop where
  year : 1<y G L x
  contracts (c f : Side) (S : StepData c f) (T : Tube G S) : S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
    PaidHere T x W κ σ B C γ H n D ∧ ∀ m : Mode, ∀ (F : Forest S.ratio) (V : Config G c) (d : Allocation G S x W),
      (∀ A,0≤rent d F V A m C γ (D m)) ∧ (∑ A, rent d F V A m C γ (D m)) ≤ 1
  clears (c f : Side) (S : StepData c f) (F : Forest S.ratio) : G.Simple → VolPrice G L →
    S.kernel=P.bind → S.patch.L=L → ∀ m β, β∈Set.Icc (y G L x/2) (2*y G L x) →
      shore S G F m β x (D m) ≤ ice G L x ^ nf f







section demonstrate
variable {P L W κ σ B H n} {C γ x : ℝ} {D : Mode → ℝ}
variable {c f : Side} {S : StepData c f} {T : Tube G S}
variable (h : Use P L W κ σ B H n C γ D x)
variable (hL : S.patch.L=L) (hN : 100*(1+radiusB x) ≤ c.val) (hF : P.Funds S T)
  (F : Forest S.ratio) (d : Allocation G S x W) (V : Config G c) (A : Stores S)
include h hL hN hF

/-- The actual leftOver and cutEntry. Includes arbitrary inert payments if
priced first, in addition to maintaining the half-earn on this sector. -/
theorem Use.left {R : Rep G f} {Λ δ w : ℝ} (hB : PortionCost d F T κ R) (hr : R.Lawful σ B Λ δ w)
    (ha : Λ≤2*p G L x) (hd : δ≤1) (hw : w ∈ Set.Icc (0:ℝ) 1) (ht : R.p.threshold = fiery G x L)
    (hb : R.beta ∈ Set.Icc (y G L x/2) (2*y G L x)) :
    let M := rent d F V A .shielded C γ (D .shielded)
    let O := outputReserve .shielded true T x R.beta V
    let E := seed G S.patch.L x κ R.beta A.shares
    let v := coin G L H n x * A.shares
    Real.exp v * earn S G x κ R.beta A.shares * leftOver d F T R A V ≤
      Real.exp R.scalar * shore S G F .shielded R.beta x (D .shielded)*Real.exp (-E/2)*O*M ∧
    (G.Simple → VolPrice G L → Real.exp v * ‖cutEntry d F T R A V‖ ≤
      Real.exp R.scalar * ice G L x ^ nf f * Real.exp (-E/2)* O * M) := by
  intro M O E v
  obtain ⟨he,hh⟩ := h.contracts _ _ _ _ hL hN hF
  obtain hz := he.full R Λ δ w hr (by rw [hL]; exact ha) hw hd (by rw [hL]; exact ht) (by rw [hL]; exact hb) F d A V .shielded
  rw [hL] at hz
  change Real.exp v * earn S _ _ _ _ _ * leftOver d F T R A V ≤ _ at hz
  unfold E; rw [hL]
  refine ⟨hz,fun hs hv => ?_⟩
  have hmr : 0 ≤ M := (hh .shielded F V d).1 A
  have ho : 0 ≤ O := (Real.exp_pos _).le
  refine (mul_le_mul_of_nonneg_left (hB.cost A V) (Real.exp_pos _).le).trans ?_
  rw [← mul_assoc]
  apply hz.trans
  gcongr
  exact h.clears _ _ _ F hs hv hF.knobs hL _ _ hb


end demonstrate
end YM.SectorNext.Remainder
