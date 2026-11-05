import YM.AnalyticBridge.RESET_INCOME_PORT.Quote
import YM.Next.SCHEDULE.Stadium
import YM.Next.UV_STRESS.Across
import YM.Push.COMMON_WITNESSES.Link
import YM.UVNext.COUPLING_RESET.Regular

set_option warningAsError false

/-!
# Cost at the post-reset template

Dial variation doesn't follow from a value (or even log-jet)
estimate on a sector! Sectors on Q x at the input don't vary with
post-reset dial. Give sufficient *separate* local conditions; pay here
without touching support exponents or posing differential requirements
on the input Curve. One case estimates the concrete E freset intended
format on all-good fields: change only the *higher* path readout with
the dial. On that case even if the price of the clover subtraction is
fully earned, charging its dial motion as if it too were cost ≤funds
could cost a different order. The clover/leading correction depends on
the incoming parameter and projections, stays FIXED here. `Carved` can
be tied to the very same early log forecast by `Clothing`. Other cases
give order-zero tests on unmasked logs producing variation. Catalog
still a separate (label and activity) prerequisite.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Next.SectorChange UVNext.CouplingReset Input RG.Supply RG.Shoot Pressure.Testing
open Push.PriceCompiler Push.BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge}
section paid
variable {b : Sheet G} {D : Rolls b} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P)
    {s : Set ℝ} {q : ResetPrices} {N m p : ℕ}

def largeOp (N : ℕ) {m p : ℕ} (V : Config G (B.a.S.side m p)) :=
  let C := (B.a.params m).clip
  let H := B.kin.path N m
  kinetic H C (B.a.budget m) V-secondTerm C H V

/-- A *derived* price on higher-order dial motion allowed by the already
purchased surplus gate. Includes equality points of the threshold. -/
lemma gate_rent (hg : ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → CubicGate D q j i x)
    (hm : m < N) {V : Config G (B.a.S.side m p)} (hV : RG.flags (B.a.budget m).threshold V=∅) :
    |largeOp B N V| ≤ sites (B.a.S.side m p)*(funds B.a m q/2) := by
  let i := B.a.clock.J (m+1)
  have hα : 1 ≤ alphaBound D i := by
    have h := B.support.kinetic N m hm
    rw [params_eq B.valid] at h
    apply le_trans _ (le_add_of_nonneg_right (abs_nonneg _))
    exact le_trans (le_add_of_nonneg_left (abs_nonneg _)) h
  have hp := hg _ _ (B.valid.pays m) _ (step_paid B.a m)
  have hs := B.support.cap N m hm.le
  have he := higher_estimate hs hV
  change |largeOp B N V| ≤ _ at he
  apply he.trans; apply mul_le_mul_of_nonneg_left _ (sites_pos _).le
  have ht := (B.a.budget m).threshold_pos; have hc := (B.a.params m).paths_pos
  apply le_trans (le_mul_of_one_le_left (by positivity) hα)
  rw [params_eq B.valid,funds,mul_div_right_comm]; exact hp

/-- One candidate all-good template equation; could require for all U
all-good. No a priori bound on the carved values or comparison to true
response meant here. Leg/loop/address continuation & applicability to
marker readings still require real construction with supports. -/
def Carved (q : ResetPrices) (s : Set ℝ) {N m p : ℕ} (F : Terms B.a m p) (V : Config G (B.a.S.side m p)) :=
  ∀ x∈s, ∃ u, ∀ a∈window B.a m q, (board B N F).add V x a=u-a*largeOp B N V

/-- Only buy per-site Slow below; this condition is not the physical
post-reset estimator (still need also off all-good, retain, masks,
validity/regularity spent, etc.). -/
def Clothing (q : ResetPrices) (s : Set ℝ) {N m p : ℕ} (F : Terms B.a m p)
    (early : ℝ → Activities G (B.a.S.side m p)) (col : ℝ → ℝ) :=
  ∀ x∈s, ∀ a∈window B.a m q, ∀ (V : Config G (B.a.S.side m p)),
    RG.flags (B.a.budget m).threshold V = ∅ →
      (board B N F).add V x a =
        (early x).additive (B.a.budget m) V - (early x).additive (B.a.budget m) 1 -
        col x*secondTerm (B.a.params m).clip (B.kin.path N m) V - (B.kin.alpha N m+a)*largeOp B N V

lemma clothed {F : Terms B.a m p} {V : Config G (B.a.S.side m p)} {early col}
    (h : Clothing B q s (N:=N) F early col) (hf : RG.flags (B.a.budget m).threshold V=∅) : Carved B q s (N:=N) F V := by
  intro x hx; refine ⟨(early x).additive (B.a.budget m) V - (early x).additive (B.a.budget m) 1 - col x*secondTerm (B.a.params m).clip (B.kin.path N m) V - B.kin.alpha N m*largeOp B N V,?_⟩
  intro a ha; rw [h x hx a ha V hf]; ring





/-- Topological order-zero variation alternatives (actual `ShapeControl`
is not part of either). Caller may issue local prices incl finite log/det
or numerator estimates through other label producers or directly carve the
kinetic read on the probe. -/
def Meter (q : ResetPrices) (s : Set ℝ) {N m p : ℕ} (F : Terms B.a m p) (V : Config G (B.a.S.side m p)) :=
  Carved B q s (N:=N) F V ∨ ∀ x∈s, ∀ a∈window B.a m q, ∀ b∈window B.a m q,
    (board B N F).varies V (funds B.a m q) x a b

lemma dial (hg : ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → CubicGate D q j i x)
    (hm : m < N) {F : Terms B.a m p} {V : Config G (B.a.S.side m p)}
    (hV : RG.flags (B.a.budget m).threshold V=∅) (h : Meter B q s (N:=N) F V)
    (hc : Catalog (board B N F) s (window B.a m q) (B.a.clock.allowance m) (B.a.clock.forcedAllowance m)) :
    ∀ x∈s, ∀ a∈window B.a m q, ∀ b∈window B.a m q,
      |(board B N F).add V x b-(board B N F).add V x a| ≤ sites (B.a.S.side m p)*funds B.a m q*|b-a| := by
  intro x hx a ha b hb
  rcases h with h|h
  · obtain ⟨u,he⟩ := h x hx
    rw [he b hb,he a ha,show u-b*largeOp B N V-(u-a*largeOp B N V)=largeOp B N V*(-(b-a)) by ring,abs_mul,abs_neg]
    have hh := gate_rent B hg hm hV
    refine mul_le_mul_of_nonneg_right (hh.trans ?_) (abs_nonneg _)
    linarith only [hh,abs_nonneg (largeOp B N V)]
  exact Template.motion hV (hc.valid x hx a ha) (hc.valid x hx b hb) (h x hx a ha b hb)
end paid
end YM.AnalyticBridge.ResetIncome
