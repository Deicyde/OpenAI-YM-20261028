import YM.Price.Waits

/-!
# Faithful stack & conditional step interface

This is a specialization of  to the needed cutoff campaigns;
we do not infer it from, or verify, the candidate sector/Gaussian argument.
Work with fixed *history-specific* path ancestry, choices, threshold & period.
`Recipe` lets subsequent producers specialize to exactly the supported
replays/adjacency predicates: for example an IR estimate may require a
particular choice of path & aperture and replay of its continuity-sensitive
renaming. Extra clauses can *constrain* the construction path but they have
no power to generate an instance or change the asserted running coupling.
All extras for a call must be supplied, and common history retains them on
that single choice. Does not assert a general vStep theorem from only bare
rep caps at arbitrary lengths/data.

E continuity across hard U queries: parameter only, fixed dictionary
(in particular fixed every forced final predicate; pack varying numeric
answers/extra variation inside the coefficient with fixed local footprint).
This is on labelled density, sup jet data NOT masked. Later E producers must
prove issues about flags/eligibility and all-choice continuity; I/O here uses
the full A stage expenditures on survivors. No shrinking exponent through
shooting across levels. No continuity across different representations assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG.Shoot
open Lattice Supply Wilson Filter Set Function
open scoped Matrix.Norms.Frobenius BigOperators ContDiff Topology
variable {G : Gauge} {n : Side} {a : Levels G}

/-- Uniform inputs at each address on the GOOD domain with (frozen)
physical flags. -/
def variesRegular (P : BudgetPoint) (X : RegularAddress n) (f g : Config G n → ℝ) (c : ℝ) :=
    0 ≤ c ∧ ∀ U, Healthy P.threshold X.support U → ∀ l, List.length l ≤ P.order →
      (∀ i ∈ l, P.dirBound X.site i) → ‖leftDerivs f l U-leftDerivs g l U‖ ≤ c

/-- Simpler charge ALL addresses (working at one fixed period when comparing,
equivalent to family hit-convergence with a constant depending on period, by
anchoring including forced). No such constant allowed in the E,K caps
of Lawful, which sit at specific stage and measure different thing!
-/
def deviation (P : BudgetPoint) (U V : Activities G n) (δ : ℝ) :=
    ∃ c d : ℕ → ℝ,
    (∀ i, variesRegular P (U.reg i) (U.E i) (V.E i) (c i)) ∧
    (∀ i, 0 ≤ d i ∧ ∀ x, ‖U.K i x - V.K i x‖ ≤ d i) ∧
    SumBudget (fun i => P.mass (U.reg i).support (c i)) δ ∧
    SumBudget (fun i => P.mass (U.forced i).support (d i)) δ

structure Curve (P : BudgetPoint) (T : ℝ → Rep G n) (X : Set ℝ) : Prop where
  beta : ContinuousOn (fun x => (T x).beta) X
  v : ContinuousOn (fun x => (T x).v) X
  reg : ∀ x∈X, ∀ y∈X,(T x).activities.reg=(T y).activities.reg
  forced : ∀ x∈X, ∀ y∈X,(T x).activities.forced=(T y).activities.forced
  continuous : ∀ ε : ℝ, 0 < ε → ∀ x∈X,
      ∀ᶠ y in 𝓝[X] x, deviation P (T x).activities (T y).activities ε

lemma Curve.mono {P : BudgetPoint} {X Y : Set ℝ} {f : ℝ → Rep G n} (h : Curve P f X) (hx : Y ⊆ X) : Curve P f Y :=
  ⟨h.beta.mono hx,h.v.mono hx,fun x a y b => h.reg x (hx a) y (hx b),fun x a y b => h.forced x (hx a) y (hx b),
    fun ε he x hz => (h.continuous ε he x (hx hz)).filter_mono (nhdsWithin_mono _ hx)⟩

def band (a : Levels G) (m : ℕ) := Icc (a.clock.hatBeta m / 2) (2*a.clock.hatBeta m)

/-- Must be filled with path data satisfying Recipe.Issues etc, for these
admitted stages. All parameters including numerical tests frozen. -/
structure Recipe (a : Levels G) where
  path (N m : ℕ) : PathData G
  retain (N m p : ℕ) : Rep G (a.S.side m p) → Prop
  first (N p : ℕ) : Rep G (a.S.side N p) → Prop
  next (N m p : ℕ) : Rep G (a.S.side m p) → Rep G (a.S.side (m+1) p) → Prop

/-- band-free return: coupling may already outside output band. -/
structure Lives (R : Recipe a) (N m p) (u : Rep G (a.S.side m p)) : Prop where
  path : u.path=R.path N m
  point : u.p=a.budget m
  clip : u.clip=(a.params m).clip
  valid : u.Lawful (a.params m).width (a.params m).paths (a.clock.loopCap m) (a.clock.allowance m) (a.clock.forcedAllowance m)
  loads : R.retain N m p u

namespace Recipe
variable (R : Recipe a)

/-- one-step return on actual coupling. Do NOT perform a step with
inapplicable β. Numbers β' real, here not required already in next band.
Record `eval` equality at ALL configurations, no contortion when flags
hit thresholds. `a` includes the actual BranchControl. -/
structure Relays (N m p) (u : Rep G (a.S.side m p)) (v : Rep G (a.S.side (m+1) p)) : Prop where
  link : u.eval = (a.clock.op m p).push v.beta v.eval
  drift : |v.beta-u.beta-G.slopeConstant*Real.log (a.S.block m).val| ≤ (a.params (m+1)).drift
  continues : R.next N m p u v

structure Starter (N p) (u : Rep G (a.S.side N p)) : Prop where
  scalars : u.v=0
  raw : u.eval=bare u.beta
  inits : R.first N p u

/-- Per-period readiness, actual producer needed. -/
structure Issues (N p) : Prop where
  initial : ∃ F, Curve (a.budget N) (n:=a.S.side N p) F (band a N) ∧
      ∀ β∈band a N,(F β).beta=β ∧ Lives R N N p (F β) ∧ R.Starter N p (F β)
  advances (m : ℕ) : m < N →
    ∀ l u : ℝ, l ≤ u → ∀ Q, Curve (a.budget (m+1)) Q (Icc l u) →
      (∀ x∈ Icc l u, Lives R N (m+1) p (Q x) ∧ (Q x).beta ∈ band a (m+1)) →
      ∃ T, Curve (a.budget m) T (Icc l u) ∧
        ∀ x∈ Icc l u,Lives R N m p (T x) ∧ R.Relays N m p (T x) (Q x)
end Recipe
end YM.RG.Shoot
