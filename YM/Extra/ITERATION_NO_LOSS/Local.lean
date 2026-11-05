import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Rebuild
import YM.Work.H01
import YM.Work.H02
import YM.Work.H03
import YM.Work.H04

/-!
# Receipts rebuilt at each invocation on one paid Levels
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Rebuild
open Filter Function Lattice Wilson RG RG.Shoot RG.Supply Precision Pressure Scales Comparison
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {S : Sheet G} {D : Rolls S} {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}
variable {a : Levels G} {V : Census} {F : Fuel D}

namespace Fuel
variable (F a)
def total (V : Census) (m : ℕ) (b : ℝ) := F.weak V (a.clock.J (m+1)) (a.clock.J m) (a.clock.hatBeta m) (a.clock.theta (a.clock.J (m+1))) b

def regular (V : Census) (m : ℕ) (b : ℝ) := F.total a V m b + F.output (a.clock.J (m+1)) (a.clock.J m) (a.clock.hatBeta m)
    (a.clock.theta (a.clock.J (m+1))) * (a.clock.threshold m)^3

def strong (m : ℕ) (b : ℝ) := F.hard (a.clock.J (m+1)) (a.clock.J m) (a.clock.hatBeta m) b
end Fuel

def kafka (a : Levels G) (m : ℕ) (c : ℝ) := Real.exp (-c*(a.clock.monitor (m+1))^2)
structure Receipt (V : Census) (F : Fuel D) (a : Levels G) (m : ℕ) : Prop where
  geometry p : Shapes.raw (a.clock.op m p).ratio (V.halo (a.clock.J (m+1)) (a.clock.J m)) (a.budget (m+1)) (a.budget m)
    (V.reserve (a.clock.J (m+1)) (a.clock.J m))
  term i : (i=m ∨ i=m+1) → Shapes.broad (V.halo (a.clock.J (m+1)) (a.clock.J m)) (a.budget i).B
    ((a.budget i).supportExponent + V.reserve (a.clock.J (m+1)) (a.clock.J m)) (a.params i).width
  reg b : b ∈ band a (m+1) → F.regular a V m b ≤ (1/2:ℝ)*a.clock.allowance m
  kin b : b ∈ band a (m+1) → (a.clock.threshold m ^ (2:ℕ))⁻¹ * F.total a V m b ≤ 1/2
  exp b : b ∈ band a (m+1) → F.strong a m b ≤ kafka a m (F.strength (a.clock.J (m+1)))
  forced : kafka a m (F.strength (a.clock.J (m+1))) ≤ a.clock.forcedAllowance m
  relative : a.clock.threshold m ≤ 2*a.clock.threshold (m+1) ∧ a.clock.threshold (m+1) ≤ 2*a.clock.threshold m
  jets : (a.budget m).order ≤ (a.budget (m+1)).order ∧ (a.budget m).power ≤ (a.budget (m+1)).power

lemma receipt (hc : Cool V F W) (hv : Open V S) (ha : Paid I a) (m : ℕ) : Receipt V F a m := by
  let j := a.clock.J (m+1); let k := a.clock.J m; let x := a.clock.hatBeta m; let y := betaF G x (D.L j)
  have hk : k ≤ j := a.fits.mono (Nat.le_succ _); have hj := a.fits.stepSlow m
  have he : a.clock.hatBeta (m+1)=y := by rw [block_beta,block_eq ha]
  have hstage (i) : a.params i=S.profile (a.clock.J i) := congr_fun ha.stage _
  have ht (i) : a.clock.threshold i = temp (a.clock.hatBeta i) := rfl
  have hh := hc.pay _ _ hk hj x (ha.pays m); have hx := a.fits.delayed m
  have hq : a.clock.allowance m=Scales.unforced x := rfl
  constructor
  · intro p
    refine ⟨?_,V.reserve_nonneg _ _,?_⟩
    · change radiusB _ ≤ 2*radiusB x; rw [he]; exact hh.geometry.1
    change 20*_*( (a.params m).supportExponent+_ ) ≤ (a.params (m+1)).supportExponent * (a.S.block m).val
    rw [block_eq ha, hstage,hstage]
    exact (hv.project j k hk hj).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (D.large _).need) (S.profile _).price_pos.le)
  · rintro i (rfl|rfl)
    · change Shapes.broad _ _ ((a.params i).supportExponent+_) _; simp_rw [hstage]; exact hh.coarse
    change Shapes.broad _ (radiusB _) ((a.params (m+1)).supportExponent+_) _; rw [he,hstage]; exact hh.fine
  · intro b hb
    change b ∈ Set.Icc _ _ at hb; rw [he] at hb
    unfold Fuel.regular Fuel.total; rw [ha.theta,ht,hq]
    change F.weak V j k x (Θ.theta j) b + F.output j k x (Θ.theta j)*_ ≤ _
    linarith only [hh.output,hh.weak b hb.1 hb.2]
  · intro b hb
    change b ∈ Set.Icc _ _ at hb; rw [he] at hb
    unfold Fuel.total; rw [ha.theta,ht, inv_mul_le_iff₀ (pow_pos (by exact Work.E09.temp_pos (by change 0 < x; linarith [show 1<x from hx])) 2)]
    have ht := unforced_threshold hx
    change Scales.unforced x ≤ _ at ht
    linarith only [ht,hh.weak b hb.1 hb.2,sq_nonneg (temp x)]
  · intro b hb
    change b ∈ Set.Icc _ _ at hb; rw [he] at hb
    unfold Fuel.strong kafka Calendar.monitor; rw [he]; exact hh.hard b hb.1
  · unfold kafka Calendar.monitor; rw [he]; exact hh.time
  · rw [ht,ht,he]; exact hh.small.symm
  exact ⟨a.fits.deepOrder (Nat.le_succ m), a.fits.deepPower (Nat.le_succ m)⟩

/-!
### Application to actual candidate curve outputs

This separate contract is not derived from Rates. Its transfer hypotheses
also include the qualitative/dictionary outputs of actually integrating the
physical measure, and may use additional (separately paid!) scheduling or
bake-specific eligibility results in their proof. No setting a decay exponent
by looking at the chosen cutoff outcome. We allow normed continuity at a
*different* support exponent but not to spend derivative order inside one
stage. `HasBudget` for magnitudes requires exponent ≥ requested. All
statements use exact functions, no dropping field-independent constants.
-/
open Input
variable {O : ChartRatio G} {K : MapPrices} {Q : PostCost D}

/-- Remaining one-step estimates/certificates just on the actual Directed,
physical band calls of its recipe. Cold startup is separate (Oust port).
Replayed predicates including any forced history must use the same data. -/
structure Actual (B : Directed G I O K Q) (V : Census) (F : Fuel D) : Prop where
  through N p m : m < N → ∀ l u : ℝ, l ≤ u → let X := Set.Icc l u
    ∀ f, Curve (B.a.budget (m+1)) f X → (∀ b ∈ X,Lives B.bake N (m+1) p (f b) ∧ (f b).beta ∈ band B.a (m+1)) →
      ∃ (s t : BudgetPoint) (g : ℝ → Rep G (B.a.S.side m p)), HasBudget s (B.a.budget m) ∧ HasJets t (B.a.budget m) ∧ Curve t g X ∧
        ∀ b ∈ X,
          (g b).eval=(B.a.clock.op m p).push (f b).beta (f b).eval ∧ B.bake.next N m p (g b) (f b) ∧
          (g b).path=B.kin.path N m ∧ (g b).p=B.a.budget m ∧ (g b).clip=(B.a.params m).clip ∧ B.bake.retain N m p (g b) ∧
          |(g b).beta-(f b).beta-B.kin.alpha N m| ≤ (B.a.clock.threshold m ^ (2:ℕ))⁻¹ * F.total B.a V m (f b).beta ∧
          (g b).activities.Valid s (F.regular B.a V m (f b).beta) (F.strong B.a m (f b).beta)

lemma program (B : Directed G I O K Q) (hc : Cool V F W) (hv : Open V S)
    (hg : ∀ j, Q.g j ≤ F.strength j) (h : ∀ N p,Bid.Oust B N p) (hB : Actual B V F) : B.Program := by
  refine ⟨fun N p => Bid.Oust.begins B (h N p) Work.H01.answer Work.H02.answer Work.H03.answer Work.H04.answer,
    fun N p m hm l v h f hf hs => ?_⟩
  obtain ⟨s,t,g,h1,h2,hc',ht⟩ := hB.through N p m hm l v h f hf hs
  refine ⟨g,h2.across hc',fun x hx => ?_⟩
  obtain ⟨he,hh,hy,hp,hr,hk,hj,hl⟩ := ht x hx; have hf := (hs x hx).2
  have hw := receipt hc hv B.valid m
  have hcost := h1.valid hl ((hw.reg _ hf).trans (mul_le_of_le_one_left (by exact Real.rpow_nonneg (by unfold Calendar.hatCoupling; positivity) _) (by norm_num)))
    ((hw.exp _ hf).trans hw.forced)
  refine ⟨he,hh,⟨by rw [hy,B.bases],hp,hr,⟨by rw [hy,hr]; exact B.support.cap N m hm.le,hp.symm ▸ hcost⟩,hk⟩, hp.symm ▸ h1.kBound hl.boundK ((hw.exp _ hf).trans ?_),
    hj.trans ((hw.kin _ hf).trans (by norm_num))⟩
  exact Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg (hg _)) (sq_nonneg _))
end YM.Extra.Iteration.Rebuild
