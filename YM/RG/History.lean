import YM.RG.Bounded
import YM.RG.Push
import YM.Gauge.Casimir

/-!
# Represented histories

These are proof-independent
interfaces for an exact history.

All constants, the kernel parameters, and
the scalar reading of the coupling belong to THAT history.

`Levels` freezes
the stage choices and the common schedule, not a class to infer.

Pre choices
are to be supplied before block ratios; Θ gates use after-ratio powers; the
budget feasibility obligations are separate and may need much more data at a
working step than is asserted **after** construction of a trajectory.

We don't
use contour or perturbative semantics in the target.

Inverse coupling definition here: β is the actual scalar in the represented
base `S_t`, with array and kinetic metric normalization conditions on flat
coefficients, remaining loop kernel without those leading Fourier coefficients,
and affine remainder vanishing, flags, addresses etc. Not a number associated to
the measure independently. This is a formulation with *existence* of such a
representation and continuation. Does not require uniqueness/reproducing an
implementation's path choice, tags unused after integration, etc. See ledger on
specialization/generalization from E; do not infer any usual beta-function claim
beyond `Running`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG

open Wilson Lattice MeasureTheory Filter Set
open scoped Matrix.Norms.Frobenius Topology BigOperators

/-- Stage-indexed choices. Chosen before `L` when costs are used
that way; do not hide `L` powers. Source cone cap included for use later. -/
structure Stage where
  clip : Clip
  order : ℕ
  power : ℕ
  supportExponent : ℝ
  width : ℝ
  paths : ℝ
  drift : ℝ
  columns : ℝ
  order_ge : 6 ≤ order
  power_ge : 2 ≤ power
  price_pos : 0 < supportExponent
  width_pos : 0 < width
  paths_pos : 0 < paths
  slow_selector : 12 ≤ clip.relaxation * width
  columns_ge : 1 ≤ columns
  drift_ge : 0 ≤ drift

/-- Fixed numerical scales and hatted coupling (threshold independent of actual shooting). -/
structure Calendar (G : Gauge) where
  schedule : Schedule
  kernel : KernelChoices
  bar : ℝ
  bar_pos : 0 < bar
  stage : ℕ → Stage
  factor : ℕ → Side
  theta : ℕ → ℝ
  J : ℕ → ℕ
  adm m : 4 ≤ J m
namespace Calendar
variable {G : Gauge} (S : Calendar G)

abbrev params (m : ℕ) := S.stage (S.J m)

def hatBeta (m : ℕ) : ℝ := S.bar + G.slopeConstant * S.schedule.scale m
def hatCoupling (m) := (Real.sqrt (S.hatBeta m))⁻¹
def monitor (m) := Real.exp ((Real.log (Real.log (S.hatBeta m)))^2)
def coverSize (m) := Nat.ceil ((Real.log (S.hatBeta m))^2)
def threshold (m) := S.hatCoupling m * S.monitor m
def allowance (m) := S.hatCoupling m ^ ((11 : ℝ)/5)
def forcedAllowance (m) := Real.exp (- ((S.monitor m) ^ ((1 : ℝ)/5)))
def loopCap (m) := 2 * (S.monitor m) ^ (S.theta (S.J m))

def op (m p : ℕ) : StepData (S.schedule.side m p) (S.schedule.side (m+1) p) where
  kernel := S.kernel
  patch := ⟨_,S.J (m+1),S.adm _, S.schedule.block_large m, S.schedule.block_odd m⟩
  sizes := (S.schedule.oneStep m p).exact_size

/-- Stage receipt in a realized trajectory. Intermediate constructors must still
supply this with the right dependency order. `Fits` constants strengthened
numerically (patch/halo buffers; schedule must pay by delay and period choice).
Not an assertion of historical feasibility. -/
structure Fits : Prop where
  mesh : S.schedule.Gentle
  sameFactor m : S.factor (S.J (m+1)) = S.schedule.block m
  monotoneL : Monotone (fun i => (S.factor i).val)
  mono : Monotone S.J
  stepSlow m : S.J (m+1) ≤ S.J m + 1
  deep : Tendsto S.J atTop atTop
  deepOrder : Monotone (fun m => (S.params m).order)
  deepPower : Monotone (fun m => (S.params m).power)
  deepExp : Monotone (fun m => (S.params m).supportExponent)
  delayed m : 1 < S.hatBeta m
  smallField m : S.threshold m ≤ 1
  sizeT m p : 100 * (S.coverSize m + 1) ≤ (S.schedule.side m p).val
  fitsPatch m p : 100 * ((S.op m p).patch.radius + 1) ≤ (S.schedule.side (m+1) p).val
  thetaRange m : 0 < S.theta (S.J m) ∧ S.theta (S.J m) ≤ ((S.J m : ℕ) : ℝ)⁻¹
  thetaMono : Antitone S.theta
  /-- For pre-L constants in the recursion. -/
  driftSmall m : (S.params (m+1)).drift / Real.log (S.schedule.block m).val ≤ ((S.J (m+1) : ℝ)^2)⁻¹
  logCost m :
    let p := S.params (m+1)
    Real.log (1 + p.paths + p.width⁻¹ + p.columns + p.clip.relaxation + p.supportExponent) /
      Real.log (S.schedule.block m).val ≤ ((S.J (m+1) : ℝ)^2)⁻¹

structure BlockControl (m p : ℕ) : Prop where
  branches : (S.op m p).patch.Branches S.kernel G
  symmetric β (U : Config G (S.schedule.side (m+1) p)) (V : Config G (S.schedule.side m p))
      (s : Signed) (b : Site (S.schedule.side m p)) :
    (S.op m p).density β (pull s ((S.op m p).ratio.embed b) U) (pull s b V) =
      (S.op m p).density β U V
  gauge β (U : Config G (S.schedule.side (m+1) p)) V t :
    (S.op m p).density β (Lattice.gauge t U) (Lattice.gauge (t ∘ (S.op m p).ratio.embed) V) =
      (S.op m p).density β U V
end Calendar

structure Levels (G : Gauge) where
  clock : Calendar G
  fits : clock.Fits
  blocks : ∀ m p : ℕ, clock.BlockControl m p
namespace Levels
variable {G : Gauge} (s : Levels G)

abbrev S := s.clock.schedule
abbrev params := s.clock.params

def budget (m : ℕ) : BudgetPoint where
  order := (s.params m).order
  power := (s.params m).power
  supportExponent := (s.params m).supportExponent
  B := s.clock.coverSize m
  threshold := s.clock.threshold m
  power_ge := (s.params _).power_ge
  order_ge := (s.params _).order_ge
  exponent_pos := (s.params _).price_pos
  B_pos := by
    have := Real.log_pos (s.fits.delayed m)
    unfold Calendar.coverSize
    exact Nat.ceil_pos.mpr (by positivity)
  threshold_pos := mul_pos (inv_pos.mpr <| Real.sqrt_pos.2 <| lt_trans zero_lt_one (s.fits.delayed m))
    (Real.exp_pos _)
  threshold_le := s.fits.smallField _

theorem transition_mass (m p : ℕ) (β : ℝ) : (s.clock.op m p).IsKernel β G :=
  (s.clock.op m p).isKernel (s.blocks m p).branches _
end Levels

variable {n : Side} {G : Gauge}

/-- Denotational representation with complete support discipline required by `Lawful`. -/
structure Rep (G : Gauge) (n : Side) where
  path : PathData G
  clip : Clip
  activities : Activities G n
  p : BudgetPoint
  beta : ℝ
  v : ℝ

namespace Rep
variable (R : Rep G n)

def exponent (U : Config G n) : ℝ :=
  R.v * Fintype.card (Site n) - R.path.inChannels R.clip R.p R.beta U - R.activities.additive R.p U

def eval (U : Config G n) := Real.exp (R.exponent U) * R.activities.gas R.p U

structure Lawful (σ C Λ δ w : ℝ) : Prop where
  paths : R.path.Bounds R.clip σ C Λ
  labels : R.activities.Valid R.p δ w

theorem exponentEnv {σ C Λ δ w : ℝ} (h : R.Lawful σ C Λ δ w) : Envelope R.exponent := by
  have g := PathData.channels_env (n := n) h.paths R.p R.beta
  have e : Envelope (R.activities.additive R.p) :=
    ⟨Activities.E_measurable h.labels.regular, (Activities.ESeries h.labels).bound⟩
  have X : Envelope R.exponent := by
    unfold exponent
    simp_rw [sub_eq_add_neg]
    exact (((Envelope.const _).add g.neg).add e.neg)
  exact X

theorem envelope {σ C Λ δ w : ℝ} (h : R.Lawful σ C Λ δ w) : Envelope R.eval := by
  exact Envelope.mul (R.exponentEnv h).exp
    (show Envelope (R.activities.gas R.p) from
      ⟨Activities.gas_measurable h.labels.forced, (Activities.gasSeries h.labels).bound⟩)
end Rep

/-- All histories under one schedule. `path` kernels/canonical terms independent of period,
not of previous finer blocking depth. Path masks fixed by Atom footprints. Normalize against
**probability** Haar. Ignore `m > N` padding; the physical measure uses level `N`. -/
structure History (G : Gauge) where
  levels : Levels G
  rep (N p m : ℕ) : Rep G (levels.S.side m p)

namespace History
variable (A : History G)
abbrev S := A.levels.S
abbrev β (N p m) := (A.rep N p m).beta

structure Conv (N p m : ℕ) : Prop where
  vac : (A.rep N p m).p = A.levels.budget m
  clip : (A.rep N p m).clip = (A.levels.params m).clip
  good : (A.rep N p m).Lawful (A.levels.params m).width (A.levels.params m).paths
    (A.levels.clock.loopCap m) (A.levels.clock.allowance m) (A.levels.clock.forcedAllowance m)
  band : A.β N p m ∈ Set.Icc (A.levels.clock.hatBeta m / 2) (2 * A.levels.clock.hatBeta m)

/-- The recurrence also records the stage-wise magnitude of the drift
(residual from the universal one-loop leading term, *not* identification of
any particular loop calculation). . -/
def Transfer (N p m : ℕ) :=
  let C := A.levels.clock
  (A.rep N p m).eval = (C.op m p).push (A.β N p (m+1)) (A.rep N p (m+1)).eval ∧
  |A.β N p (m+1) - A.β N p m - G.slopeConstant*Real.log (A.S.block m).val| ≤
    (C.params (m+1)).drift

def Running := ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ N p,
    m ≤ N → |A.β N p m - A.levels.clock.hatBeta m| ≤ ε * A.S.scale m

/-- Endpoint history cuts (more intermediate gates can be used to construct
these proofs). -/
structure Selected : Prop where
  path_shared (N p q m : ℕ) : m ≤ N → (A.rep N p m).path = (A.rep N q m).path
  represents (N p m : ℕ) : m ≤ N → A.Conv N p m
  starts (N p : ℕ) : (A.rep N p N).v = 0 ∧ (A.rep N p N).eval = bare (A.β N p N)
  steps (N p m : ℕ) : m < N → A.Transfer N p m
  reaches (N p : ℕ) : A.β N p 0 = A.levels.clock.bar
  running : A.Running

theorem partition_eq (h : A.Selected) (N p m : ℕ) (hv : m ≤ N) :
    (∫ U, (A.rep N p m).eval U ∂prior G (A.S.side m p)) = partition G (A.S.side N p) (A.β N p N) := by
  induction hv using Nat.decreasingInduction with
  | self => rw [(h.starts N p).2]; rfl
  | of_succ k hk H =>
    rw [(h.steps N p k hk).1]
    rw [StepData.push_integral (A.levels.transition_mass ..) _
      (((A.rep N p (k+1)).envelope (h.represents _ _ _ hk).good).integrable _), H]
end History
end YM.RG
