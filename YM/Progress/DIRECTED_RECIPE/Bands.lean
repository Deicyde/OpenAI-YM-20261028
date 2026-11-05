import YM.Progress.DIRECTED_RECIPE.Handoff
import YM.Progress.DIRECTED_RECIPE.Selected

/-!
# Closing the availability obligations of the recipe

See `RCake` etc in reader docs. NO assumption of `Issues`, `Oust` or
`Program` in these closure results. Instead accept pre-assembly estimates on
the real integrals, still expensive and red. Spell out the conditional producer
obligations (`Origins` and `Invoices`) in Wilson startup and in implementing
vStep, *at the exact* Levels and kinetic plan to be used. This is one possible
sufficient route. E.g. extra +1 reserve on pre-fusion hard/soft may need more
support control in RRequirements; step *at same exponent* uses Full curve
hypothesis. Not assuming we can find estimates from arbitrary Regime, nor that
the proposed proof in E achieves these interfaces.

Deduce, not assume, the `Recipe.retain,first,next` predicates on all outputs,
gather the exp-log packet, choose scalar & preserve normalizer, obtain the
post estimates (with order usable for the next step), and prove actual all-curve
availability on THIS B with its shared dictionary. Use verified H04 (using even
the `X.little` required in Oust); the cooking obligations at steps themselves
will only use the sampling set dominating result.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG Wilson Lattice RG.Shoot Ovens Ovens.Pipes Input Precision
open Next.Scheduling RG.Supply MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {a : Levels G} {M : Horizon a} {O : ChartRatio G}
variable {s : Survey G} {K : MapPrices} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
variable {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y} {mould : Beam K D}

/-- Sufficiency input for Wilson startup, in addition to kinetic/etc. X not
stipulated to be on the canonical shelves! Note `little` here, common over the
whole actual cutoff band, as required by `Bid.Oust`. Even when there is no step.
For the default `permissions`, the `.permit` in SurfacePay is free. -/
structure Menu (k : Kin M O) (r : Permissions a) (N p : ℕ) (X : Pipes G (a.S.side N p))
    (d : ℝ → Tap G (a.S.side N p)) : Prop where
  law : ∀ β∈band a N, SurfacePay k r N p β X (d β)
  curve : Curve (a.budget N) (Bid.Cake d X (k.path N N) (a.params N).clip (a.budget N)) (band a N)
  atoms : invariantJet (a.budget N) d (band a N)
  common : X.little (a.budget N) d (band a N)

def Origins (k : Kin M O) (r : Permissions a) := ∀ N p, ∃ X d, Menu k r N p X d

/-- Advance input charge record at actual Ingress Q. In particular
`SurfacePay` and `BatchPay` via `Ingredients` use BEYOND individual cap
estimates (X labelled population with joint bills over old hard and new soft).
`BatchPay` on these **post-L** shapes at positions m includes explicitly the
same analytic constants even for same-stage loops and any p. Missing nonlinear
estimate, needs additional producer purchasing obligations. `switches` uses
these data *uniformly through* every beta variation. Allows the subsubsequence
test from : whenever an incoming tested sequence of parameters on this
Curve ALSO observes an A-norm common domination within the indicated (positive)
slack, the chosen raw output data must support a summable domination on further
sampling of those parameters. Pointwise bounds alone will not discharge this. -/
structure Draft (k : Kin M O) (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (r : Permissions a) (N m p : ℕ)
    (Q : ℝ → Rep G (a.S.side (m+1) p)) (Z : Set ℝ) (Δ : ℝ → ℝ)
    (X : Pipes G (a.S.side m p)) (d : ℝ → Tap G (a.S.side m p)) : Prop where
  ingredients : ∀ x ∈ Z, BatchPay k e F r N m p (Q x) (Δ x) X (d x)
  switchβ : ContinuousOn Δ Z
  individual : Flow (a.budget m) d X Z
  switches : Passage (a.budget (m+1)) Q (a.clock.allowance (m+1)) (a.clock.forcedAllowance (m+1))
    (a.budget m) d X Z

def Ingress (k : Kin M O) (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (r : Permissions a) (N m p : ℕ)
    (Q : ℝ → Rep G (a.S.side m p)) (Z : Set ℝ) :=
    Curve (a.budget m) Q Z ∧ ∀ x∈Z, PeriodFuture k e F r N p m (Q x) ∧ (Q x).beta∈band a m

/-- Future RAdvances input to still prove, not a conclusion implied by RLoops
or just a conjunction of point-wise availabilities for singleton intervals.
At every p after the levels chosen, *incl at m=0*, over any genuine Curve
whose inputs are all within bands, with pointwise replay predicate from the
cutoff. Real per-call constants and sector inputs in those same Levels must
pay these, including `Q` not given as a continuous family of whole replays.
Values outside Icc l u are padding, no assertion. -/
def Invoices (k : Kin M O) (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (r : Permissions a) :=
    ∀ N p m, m < N → ∀ l u : ℝ, l ≤ u → ∀ Q, Ingress k e F r N (m+1) p Q (Icc l u) →
      ∃ Δ X d, Draft k e F r N m p Q (Icc l u) Δ X d

variable {k : Kin M O} {e : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage} {r : Permissions a} {N m p : ℕ}

namespace Menu
variable {X d} (H : Menu k r N p X d)

/-- Thus the startup team may design on ANY dictionaries and use the packing
operation in Batch at the end. No substantive startup estimates here. -/
theorem shelves (e : ℕ → ℕ → Exchange) (paid : Paid I a) (hM : M.Suffices K) (ho : LocalRatio O)
    (hk : k.Planned (mould.price F)) (H : Menu k r N p X d) : Bid.Oust (prepared k e F r paid hM ho hk) N p := by
  refine ⟨drawer G _, fun i => Rack.widen X (d i), folio G _, ?_⟩
  exact ⟨⟨Rack.raw_curve X _ _ _ _ H.curve,Rack.uniform_atoms X H.atoms,Rack.common_hit H.common⟩,
    fun β hx =>
      ⟨⟨PeriodFuture.begin hx (H.law β hx), hx, _, _, H.law β hx,rfl⟩,
        by
          have h := (H.law β hx).ingredients
          obtain ⟨κ,γ,u,hH,hJ,hj⟩ := h.to_shelves.pays
          refine ⟨κ,γ,u,hH,hJ,hj,fun i => ?_⟩
          have he := (H.law β hx).matches_raw i
          exact Eq.trans (congrArg₂ (· * ·) (congr_fun
            (Rack.raw_eval (f:=d) X (k.path N N) (a.params N).clip (a.budget N) β) i)
            (congr_arg Real.exp (Rack.same_log X (d β) i))) he⟩⟩

lemma starts (H : Menu k r N p X d) : Curve (a.budget N) (fun x => fromTop k N p x X (d x)) (band a N) :=
  Work.H04.answer G _ _ (fun j => Rack.widen X (d j)) (folio G _) _ _ _ _
    (Rack.raw_curve X _ _ _ _ H.curve) (Rack.uniform_atoms X H.atoms) (Rack.common_hit H.common)

lemma engages (H : Menu k r N p X d) (e F) : Ingress k e F r N N p (fun x => fromTop k N p x X (d x)) (band a N) :=
  ⟨H.starts, fun i hx => ⟨PeriodFuture.begin hx (H.law i hx), hx⟩⟩
end Menu

namespace Draft
variable {Δ d X} {Z : Set ℝ} {Q : ℝ → Rep G (a.S.side (m+1) p)}

/-- One response on the full parameter set, after proving its scalar computation
makes sense and paying the particular pre-assembly estimates. -/
lemma reload_all (H : Draft k e F r N m p Q Z Δ X d) (g : Ingress k e F r N (m+1) p Q Z)
    (paid : Paid I a) (tax : Regime mould e F W) (hk : k.Planned (mould.price F)) (hh : IsCompact Z) :
    Curve (a.budget m) (fun x => receive k N m p (Q x) (Δ x) X (d x)) Z := by
  have hp y (he : y∈Z) := ((g.2 y he).1).packed paid tax hk
  refine switched g.1 ?_ H.individual H.switches
    ((g.1.beta.add continuousOn_const).add H.switchβ) (scalar_curve hh g.1 (fun i h => (hp i h).lives)
    (fun i h => (hp i h).continuous) (fun i h => (hp i h).continues 1)) ?_
  · intro x hx
    have he := (hp x hx).lives
    exact he.point ▸ he.valid.labels
  intro x hx
  obtain ⟨_,_,u,h,_,_⟩ := (H.ingredients x hx).ingredients.pays
  exact ⟨_,u,h⟩

lemma returns (H : Draft k e F r N m p Q Z Δ X d) (g : Ingress k e F r N (m+1) p Q Z)
    (paid : Paid I a) (tax : Regime mould e F W) (hM : M.Suffices K)
    (hT : LocalRatio O) (hk : k.Planned (mould.price F)) :
    let B := prepared k e F r paid hM hT hk
    ∀ x∈Z, B.Move N m p (receive k N m p (Q x) (Δ x) X (d x)) (Q x) :=
  fun x hx => firing (H.ingredients x hx) (g.2 x hx).2 (g.2 x hx).1 paid tax hM hT hk
end Draft

theorem programs (paid : Paid I a) (tax : Regime mould e F W) (hM : M.Suffices K)
    (hT : LocalRatio O) (hk : k.Planned (mould.price F)) (g : Origins k r) (hF : Invoices k e F r) :
    (prepared k e F r paid hM hT hk).Program := by
  refine ⟨fun N p => ?_,fun N p m hh l u hi Q hq hp => ?_⟩
  · obtain ⟨X,d,H⟩ := g N p
    refine ⟨fun i => fromTop k N p i X (d i), H.starts,fun i hi => ?_⟩
    exact ⟨rfl, begun (H.law i hi) hi _ hk, starter (H.law i hi) hi _ _⟩
  have He : Ingress k e F r N (m+1) p Q (Icc l u) :=
    ⟨hq, fun i hi => ⟨(hp i hi).1.loads, (hp i hi).2⟩⟩
  obtain ⟨Δ,X,d,H⟩ := hF N p m hh l u hi Q He
  exact ⟨_, H.reload_all He paid tax hk isCompact_Icc,H.returns He paid tax hM hT hk⟩
end YM.Progress.DirectedRecipe
