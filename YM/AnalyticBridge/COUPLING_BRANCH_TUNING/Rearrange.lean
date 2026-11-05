import YM.AnalyticBridge.COUPLING_BRANCH_TUNING.Lens
import YM.AnalyticBridge.COUPLING_BRANCH_TUNING.Reading
import YM.Push.LOCAL_SPLITTING.Calculus


set_option warningAsError false

/-!
# Regular-label comparison AROUND the coupling normalization

One sufficient concrete template spelling to earn a before-to-after `RegularDrift`. Formalizes
variation cost of -type operations. Work on common
addresses. The formula is on *unmasked payloads* or their actual germs; it is an input about the
candidate in addition to other hypotheses in `Candidates`, and sufficient here to avoid having to
pay its E variations directly. Does NOT authorize assuming compatibility with `Kin.alpha`,
projector/compiler estimates, or exact evaluator identity. It doesn't derive from a packet
identity (nor prove the bookings in E succeed on these particular labels). The identity,
wrapping/address payments and the projection agreement all have to be supplied on actual data if
buying these prices. Clover patterns and heat and higher-atom rewrites represented by their actual
functions (can include signs & constants in them); this portion only cares about their direction
budgets/linearity below, not a stencil identity with the curvature. Requires sufficient b fits
also on enlarged supports, and the inputs globally readable with these addresses (can use spare
labels when expanding). This cut has no clipping comparisons in the K-gas (Shape and continuity
requirements and additional comparison on newly attached/fused K still separate).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.BranchTuning.AffinePay
open Lattice Wilson RG Shoot Function Filter UVNext.CouplingReset Next.Foundations Push.Local
open scoped Matrix.Norms.Frobenius BigOperators Topology ContDiff Classical
variable {G : Gauge} {n : Side} {P : BudgetPoint} {ι : Type*} [Fintype ι]

/-- Freeze prescriptions on the candidate. Use separate `pattern` terms for the signed clover
subtractions under a finite list of curvature tests (allow polarization & constants in the
pattern; test curvature direction can be scaled consistently); `warp` for terms multiplied by
the common normalization reading (response clovers minus the actual atoms, higher-curvature
charged atoms etc.); and `staticTerm` for unvarying path terms e.g. α currents. If using a
projection canceling them, use genuinely enough tests and use the signed functions that realize
the identity below. No working assertion that this is sufficient for ShapeControl or for
packing/translation. -/
structure Layout (P : BudgetPoint) (G : Gauge) (n : Side) (ι : Type*) where
  lens : Lens P G n ι
  targetAddr : ℕ → RegularAddress n
  larger i : (lens.source i).support ⊆ (targetAddr i).support
  aligned i : (lens.source i).site = (targetAddr i).site
  anchor : Site n
  standard : ι
  pattern : ℕ → ι → Config G n → ℝ
  warp : ℕ → Config G n → ℝ
  staticTerm : ℕ → Config G n → ℝ

namespace Layout
variable {L : Layout P G n ι}







/-- Primitive costs necessary only on the fixed, pre-mask pieces (no x dependence).
All summability per-anchor. `α` etc. if entering `staticTerm` must be the bought one.
Layout enlargement can cost E-weight for the full support enlargement; book at `R`.
No idealizations about `ℓ'` path tails. -/
structure Price (L : Layout P G n ι) (R C D : ℝ) : Prop where
  expand_nonneg : 0 ≤ R
  head_nonneg : 0 ≤ C
  complexity_nonneg : 0 ≤ D
  expands i (b : ℝ) : 0 ≤ b → P.mass (L.targetAddr i).support b ≤ R * P.mass (L.lens.source i).support b
  patterns i j : P.supBounds (L.targetAddr i).site (L.targetAddr i).support (L.pattern i j) (C * P.threshold^2)
  atoms : ∃ b : ℕ → ℝ, (∀ i, P.supBounds (L.targetAddr i).site (L.targetAddr i).support (L.warp i) (b i)) ∧
    ∀ o, SumBudget (fun i => if (L.targetAddr i).site=o then P.mass (L.targetAddr i).support (b i) else 0) (D * P.threshold^2)
  regular i U : Healthy P.threshold (L.targetAddr i).support U →
    Chart P.order (L.warp i) U ∧ Chart P.order (L.staticTerm i) U ∧ ∀ j, Chart P.order (L.pattern i j) U

variable {R C D u v : ℝ} {S F : Activities G n} {r : ℕ}









end Layout
end YM.AnalyticBridge.BranchTuning.AffinePay

namespace YM.AnalyticBridge.BranchTuning
open Lattice Wilson RG Shoot RG.Supply Input Precision Set Function Push.Local UVNext.CouplingReset
open scoped Matrix.Norms.Frobenius BigOperators Topology ContDiff Classical
variable {G : Gauge} {ι : Type*} [Fintype ι] {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W}
    {I : Wait Y} {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {B : Directed G I Z K P} {m N p : ℕ}
    {q : ResetPrices} {r : Rates} {η : ℕ → ℝ} {u : ℝ → ℝ} {s : Set ℝ}
    {F : ℝ → Activities G (B.a.S.side m p)} {S : ℝ → Activities G (B.a.S.side m p)}
    {Q : In B.a m p} {V : Config G (B.a.S.side m p)}

section
variable {n : Side} {T : BudgetPoint} {d : ℕ} {A E : ℝ} (h : Activities G n)


end


end YM.AnalyticBridge.BranchTuning
