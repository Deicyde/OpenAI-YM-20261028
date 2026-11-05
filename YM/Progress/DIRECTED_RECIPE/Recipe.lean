import YM.Next.SCHEDULE.Dues
import YM.Progress.DIRECTED_RECIPE.Batch


/-!
# Recipe from the kinetic plan

The choice of recipe will include fixed paths *across periods*, ancestry indexed
by N, and the obligations to bake at each level. Numbering like `Calendar.op`:
step is m+1 to m. All price rows frozen before choosing Bar, incl pre-L charges
(e), after-L envelopes (F) and numerical delay tests (`Regime`).

Not arbitrary Lawful inputs: use `PeriodFuture` as the retain predicate. Only
actual Wilson replays, with surviving inputs and accountable predecessors, can
be used for further advents. No assumption on results staying within the band.
Continuity tests separate. In particular being offered a Curve on `[l,u]` of
such representatives does *not* require as input that it is the continuous output of a single
trial trajectory. Each point will nevertheless have these certificates, (whenever the numerical and upstream plan premises used below hold), and the
step implication we use must hold on the whole parameter set as stated.

Recall is important if wanting to restrict to particular integration algorithms
subsequently. Here the flags, names, pre-assembly census (at that point), actual
density relations and uniformity receipts are enough. If needing extra
fine-to-coarse genealogy inside integrations (e.g., specific ports for marks),
clients may use `Permissions` to track such point/edge properties. This *costs
new proofs* on actual outputs. No claim of automatic extra marker funding or
that the Programs for distinct choices are the same! Default recipe has no such
extra filters; all the estimates required in even this case are substantive.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG Wilson Lattice RG.Shoot Ovens Ovens.Pipes Input Precision
open Next.Scheduling RG.Supply MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {a : Levels G} {M : Horizon a} {O : ChartRatio G}
variable (k : Kin M O) (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage)

section Bills
/-- The fees in this recipe are from `recloses`; `e` pre-L,
`F` after L (both i=j and i=j-1). Need to produce estimates of these
shapes or better already at these prices; will not derive nonlinear cost
assertions as implied by scheduling. -/
def portion (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (a : Levels G) (m : ℕ) (β : ℝ) :=
  let C := a.clock; let j := C.J (m+1); let i := C.J m; let c := (e j i).cost; let f := F j i
  c * f.switch Instrument.plain c (a.S.block m).val (C.theta j) (C.hatBeta m)
    (C.hatBeta (m+1)) (Clock.gap β)

def Echarge (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (a : Levels G) (m : ℕ) (β : ℝ) :=
  let C := a.clock; let j := C.J (m+1); let f := F j (C.J m)
  portion e F a m β + f.bundle Instrument.plain (C.theta j) (C.hatBeta m) (C.hatBeta (m+1)) * (C.threshold m)^(3:ℕ)

def Kcharge (F : ℕ → ℕ → Postage) (a : Levels G) (m : ℕ) (β : ℝ) :=
  let C := a.clock; let j := C.J (m+1); let f := F j (C.J m)
  f.H * Real.exp (-f.rate * ((C.threshold (m+1))/Clock.gap β)^(2:ℕ))

-- v' in exponent normalized per Site at scale m, NOT by number of bonds

def flatRate (a : Levels G) (m p : ℕ) (Q : Rep G (a.S.side (m+1) p)) : ℝ :=
  Real.log ((a.clock.op m p).push Q.beta Q.eval 1) / Fintype.card (Site (a.S.side m p))

def fromTop (N p : ℕ) (β : ℝ) (X : Pipes G (a.S.side N p)) (d : Tap G (a.S.side N p)) :=
  finish (k.path N N) (a.params N).clip (a.budget N) X d β 0

def receive (N m p : ℕ) (Q : Rep G (a.S.side (m+1) p)) (Δ : ℝ) (X : Pipes G (a.S.side m p)) (d : Tap G (a.S.side m p)) :=
  finish (k.path N m) (a.params m).clip (a.budget m) X d (Q.beta + k.alpha N m + Δ) (flatRate a m p Q)
end Bills

/-- Can bind to particular ingress or include extra estimates. Quantified so
that producer MUST discharge any such further requirements. -/
structure Permissions (a : Levels G) where
  starts (N p : ℕ) (β : ℝ) (X : Pipes G (a.S.side N p)) (d : Tap G (a.S.side N p)) : Prop
  follows (N m p : ℕ) (Q : Rep G (a.S.side (m+1) p)) (Δ : ℝ)
    (X : Pipes G (a.S.side m p)) (d : Tap G (a.S.side m p)) : Prop

def permissions (a : Levels G) : Permissions a := ⟨fun _ _ _ _ _ => True, fun _ _ _ _ _ _ _ => True⟩

variable (r : Permissions a)

/-- Exact upstream RCake input fees (not from Kin alone). Does not assume
recipe retain or anything about labels coming out of the gathering. Later
also need per-band readiness using ONE X and fixed tests through β. -/
structure SurfacePay (N p : ℕ) (β : ℝ) (X : Pipes G (a.S.side N p)) (d : Tap G (a.S.side N p)) : Prop where
  ingredients : Ingredients X d (a.budget N) (a.clock.allowance N) (a.clock.forcedAllowance N)
  matches_raw U : (trunk (k.path N N) (a.params N).clip (a.budget N) X d β 0).eval U *
    Real.exp (∑' l, d.logarithm l U) = Wilson.bare β U
  permit : r.starts N p β X d

/-- One possible set of invoices to RAdvances/estimation tasks, in the
faithful parameter conventions of this Schedule. Input β in triggering band
when these are asked for. X = real labelled population *before* final
forced attachment accounting. Need estimates on actual outputs of RG (e.g.
after recovering support powers from inherited supports), not projections from
regime inequalities. Quote has to pay K with the strong post-L reserve. Ratio
in `splitting` includes all canonical pieces in `trunk.path`, genuine coupled
block integral using `Q.beta` and real V, with indicators only as in RG. The
per-site scalar will be obtained separately. We expose this precursor, not a
proof of these integral estimates or of the kinetic correction algorithm.
See . -/
structure BatchPay (N m p : ℕ) (Q : Rep G (a.S.side (m+1) p)) (Δ : ℝ)
    (X : Pipes G (a.S.side m p)) (d : Tap G (a.S.side m p)) : Prop where
  ingredients : Ingredients X d (a.budget m) (Echarge e F a m Q.beta) (Kcharge F a m Q.beta)
  splitting U : (trunk (k.path N m) (a.params m).clip (a.budget m) X d (Q.beta + k.alpha N m + Δ) 0).eval U *
      Real.exp (∑' i, d.logarithm i U) =
        (a.clock.op m p).push Q.beta Q.eval U / (a.clock.op m p).push Q.beta Q.eval 1
  bill : (a.clock.threshold m)^(2:ℕ) * |Δ| ≤ portion e F a m Q.beta
  permit : r.follows N m p Q Δ X d

/-- The *finer* levels, exact period. Index N cutoff as usual. At no point
assume the current output can make a new transfer. -/
inductive PeriodFuture (k : Kin M O) (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (r : Permissions a)
    (N p : ℕ) : (m : ℕ) → Rep G (a.S.side m p) → Prop
  | begin {β X d} : β ∈ band a N → SurfacePay k r N p β X d → PeriodFuture k e F r N p N (fromTop k N p β X d)
  | struck {m} {Q Δ X d} : m < N → PeriodFuture k e F r N p (m+1) Q → Q.beta ∈ band a (m+1) →
      BatchPay k e F r N m p Q Δ X d → PeriodFuture k e F r N p m (receive k N m p Q Δ X d)

def recipe : Recipe a where
  path := k.path
  retain N m p := PeriodFuture k e F r N p m
  first N p u := u.beta∈band a N ∧
    ∃ X d, SurfacePay k r N p u.beta X d ∧ u = fromTop k N p u.beta X d
  next N m p u v := m<N ∧ v.beta ∈ band a (m+1) ∧
    ∃ Δ X d, BatchPay k e F r N m p v Δ X d ∧ u = receive k N m p v Δ X d

/-- The directed choice on a SOMEDAY funded Schedule. Parametric in any
stage/paid data where the *same* Levels, Horizon and (post-L) path plan are
paid. This is the constructor; the substantive readiness of its predicates
for the kickoff and for all rollout calls is in the accompanying theorems.
No assertion that there is ever a `Kin.Planned` (nor that different numerical
prices than used here automatically support the reclosure theorems). -/
def prepared {P : Sheet G} {D : Rolls P} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {K : MapPrices} {F' : PostCost D} (h : Paid I a) (hM : M.Suffices K)
    (ho : LocalRatio O) (hk : k.Planned F') : Directed G I O K F' :=
  ⟨a,h,ho,M,k,hM,hk,recipe k e F r,rfl⟩

section Storage
variable {k e F r} {N m p : ℕ} {R : Rep G (a.S.side m p)} {Q : Rep G (a.S.side (m+1) p)}
lemma starter {X d β} (v : SurfacePay k r N p β X d) (w : β ∈ band a N) (e F) :
    (recipe k e F r).Starter N p (fromTop k N p β X d) := by
  refine ⟨rfl,?_, w,_,_,v,rfl⟩
  funext U
  exact (v.ingredients.unshifted (k.path N N) (a.params N).clip β 0 U).trans (v.matches_raw U)

namespace PeriodFuture
lemma pockets (h : PeriodFuture k e F r N p m R) :
    m ≤ N ∧ R.p = a.budget m ∧ R.path = k.path N m ∧ R.clip = (a.params m).clip ∧
    HasSlots (a.budget m) R.activities := by
  cases h with
  | begin w h => exact ⟨le_rfl,rfl,rfl,rfl, h.ingredients.spare_room ..⟩
  | struck hj H hq h => exact ⟨hj.le,rfl,rfl,rfl,h.ingredients.spare_room ..⟩
end PeriodFuture

lemma actual_eval {X d Δ} (h : BatchPay k e F r N m p Q Δ X d)
    (hp : 0 < (a.clock.op m p).push Q.beta Q.eval 1) :
    (receive k N m p Q Δ X d).eval = (a.clock.op m p).push Q.beta Q.eval := by
  funext U
  unfold receive
  rw [h.ingredients.exact_eval,h.splitting,flatRate,div_mul_cancel₀ _ ?_,Real.exp_log hp,mul_div_cancel₀ _ hp.ne']
  exact_mod_cast (Fintype.card_ne_zero (α:=Site (a.S.side m p)))
end Storage
end YM.Progress.DirectedRecipe
