import YM.UVNext.COUPLING_RESET.Advance
import YM.UVNext.COUPLING_RESET.Normalized




set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Optional quantitative inverse tuning of a finite multi-step band family

Different direction than the correction dial. Typically start with the
result of `families` for the unmarked estimates in hand; need not assume
a continuous selector through arbitrary multiple disconnected components of
survival parameters. For a controlled INVERSE (reparametrizing that whole
trajectory by the beta ultimately read at its bottom), give more specific
sufficient hypotheses on the real response and the regular labels at each
handoff. Proportional error conditions via all the finer kernels at once,
including across closed intervals, not claiming these from absolute
cumulant bounds or each step's stationary-loop estimates. Do not
need coherent field derivatives of actual representatives off their good
domains. The inverse Lipschitz price can deteriorate with depth; no uniform
inverse even through all the repeated stages claimed. The move budgets on
the newly parametrized band do NOT deteriorate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open MeasureTheory Push.BetaTransport Lattice Wilson RG RG.Shoot RG.Supply Input Precision Function Set Filter
open scoped Matrix.Norms.Frobenius Topology BigOperators

variable {G : Gauge}



variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {B : Directed G I Z K P} {η : ℕ → ℝ} {q : ResetPrices}
    {N m p i : ℕ}

def knob {a : Levels G} (F : ℝ → Trail a p) x k := (F x k).beta

def key (B : Directed G I Z K P) (N i : ℕ) {p : ℕ} (V : Config G (B.a.S.side i p)) := kinetic (B.bake.path N i)
    (B.a.params i).clip (B.a.budget i) V

/-- Bounds are on the ALREADY obtained family's data; segments of the beta
arrays away from their endpoints need not be themselves physically reached
but the comparison has to price *those* normalized Wilson/kernel integrals.
Strong (full-band-family) hypotheses when paths are long or volume grows.
These asking prices are in units of a positive signal at the tested field,
not WilsonCap/noiseCap-type absolute derivative bounds without leading terms.
-/
structure Signal (B : Directed G I Z K P) (p N m : ℕ) (F : ℝ → Trail B.a p) (s : Set ℝ)
    (V : ∀ i, Config G (B.a.S.side i p)) : Prop where
  weak i : m ≤ i → i < N → flags (B.a.budget i).threshold (V i) = ∅
  kinetic i : m ≤ i → i < N → 0 < key B N i (V i)
  error i : m ≤ i → ∀ h : i < N, ∀ x∈s, ∀ y∈s,
    let b := knob F; let κ := key B N i (V i); let Δ := b y (i+1) - b x (i+1)
    ∀ z ∈ Icc (0:ℝ) 1, |Δ*κ - ratioChange B.a p N (join b x y) (b y-b x) h.le (V i) z| ≤ |Δ| * κ/4
  activities i : m ≤ i → i < N → ∀ x∈s, ∀ y∈s,
    let E := fun t => (F t i).activities.additive (B.a.budget i) (V i)
    |E y-E x| ≤ |knob F y (i+1)-knob F x (i+1)| * key B N i (V i)/4

variable {s : Set ℝ} {F : ℝ → Trail B.a p} {V : ∀ i, Config G (B.a.S.side i p)}













section OneStep
variable {hm : m < N} {b : BetaCurve} {Q : In B.a m p} {U : Config G (B.a.S.side m p)} {f : Terms B.a m p}

/-- Alternative direct-step gain method BEFORE correcting with `correct`, so
pay the extra estimates during production of Income if achievable. Do not
bound labelled differences assuming the corrected scalar map already known to
be Lipschitz. Pay the incoming-parameter change on additive with `t` fixed
(the SAME additive coupling error beyond the predictors at x,y). Together
with dial monotonicity instead of `Signal.activities` after root-finding this
earns proportional gain at a Prefix output. Response-error tester for routes
preparing it together with e.g., `crossings`. -/
structure Increment (h : m < N) (B : Directed G I Z K P) (p : ℕ) (q : ResetPrices) (s : Set ℝ)
    (b : BetaCurve) (U : Config G (B.a.S.side m p)) (f : Terms B.a m p) : Prop where
  errors : ∀ x∈s, ∀ y∈s, let Δ := b y (m+1)-b x (m+1); let κ := key B N m U
    ∀ z∈Icc (0:ℝ) 1, |Δ*κ - ratioChange B.a p N (join b x y) (b y - b x) h.le U z| ≤ |Δ| * κ / 8
  acts : ∀ x∈s, ∀ y∈s, ∀ t ∈ window B.a m q,
    let E z := (board B N f).add U z t
    |E y - E x| ≤ |b y (m+1)-b x (m+1)| * key B N m U / 8


end OneStep
end YM.UVNext.CouplingReset
