import YM.Next.FLUCTUATIONS.Grants
import YM.Push.PRICE_COMPILER.Basic
import YM.Work.A15
import YM.Work.B17

/-!
# Using the Grants without inspecting a candidate Schedule

Strengthen the existing `pricing_order` usage pattern for the multi-requirement
price compiler. All adjacencies include within-one-stage calls. The *transition*
sizes w will be chosen AFTER-L but BEFORE choosing θ, since more uses may need
to price powers involving w before θ. β prices depend on the **actual** w;
can't automatically reuse for larger w. They and the scale entry can be raised
independently after choosing w. Here w is the pressure price parameter (`W₀`
in E), NOT a gas weight.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG Wilson RG.Supply Pressure Pressure.Teller Pressure.Testing
open Precision Input Tree
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

/-- Demand for a length. Does not need the history. Arguments `(finer,coarser)`. -/
def PressureGate (p : Sheet G) (K : MapPrices) (j i : ℕ) (L : Side) := ∀ᶠ w : ℝ in atTop,
    ∃ μ : ℝ, 0 < μ ∧ cash (Testing.query p K j i) L w μ

/-- Use `FLUCTUATIONS` actual Grants. Given p profile and K this pre-L piece
requires just a lower threshold on lengths L(j). Changing `floorL` doesn't
change the demand. The predicate for a single length itself does *not*
assert monotonicity in length. -/
theorem pressureFloors (p : Sheet G) (K : MapPrices) :
    ∃ f : ℕ → ℕ, Monotone f ∧ p.floorL ≤ f ∧ ∀ j L, f j ≤ L.val →
      ∀ i, StepStages j i → PressureGate p K j i L := by
  choose b hb using fun j i => (Next.Fluctuations.grants (Testing.query p K j i)).precedes
  let u (j : ℕ) := max (p.floorL j) (fromMax b j)
  refine ⟨prefixHi u, prefixHi_mono _, fun _ => (le_max_left ..).trans (le_prefixHi u le_rfl),
    fun j L hl i he => hb j i L ?_⟩
  exact le_trans ((le_fromMax b he).trans (le_max_right ..)) ((le_prefixHi u le_rfl).trans hl)

section
variable {p : Sheet G} {D : Rolls p} {K : MapPrices}

structure Charges (K : MapPrices) (D : Rolls p) (w : ℕ → ℕ → ℝ) (entry rate : ℕ → ℝ) : Prop where
  fee j i : 0 < w j i
  ent : Monotone entry
  start j : 1 ≤ entry j
  pos j : 0 < rate j
  rates : Antitone rate
  earn j i (h : StepStages j i) x (hp : entry j ≤ x) : Teller.live (Testing.query p K j i) (D.L j) (w j i)
      (fun S T _ A y U k V => rate j*(fiery G y (D.L j))^2 * A.shares ≤ A.assessed T y U (S.prediction U k) V) x

/-- Price ORDER statement *usable before choosing protection*. At a D after
L, buy the ability to charge W as large as desired (and all constraints per
transition simultaneously), from the grant already bought. Then for the w
actually chosen get μ and entry floors, independent of Theta or Delays. -/
theorem charges (h : ∀ j i, StepStages j i → PressureGate p K j i (D.L j)) :
    ∃ k : ℕ → ℝ, Monotone k ∧ (∀ j, 1 ≤ k j) ∧ ∀ w : ℕ → ℕ → ℝ, (∀ j i, k j ≤ w j i) →
      ∃ F μ : ℕ → ℝ, Charges K D w F μ := by
  obtain ⟨k,hk,h₁,hK⟩ := collect_upper (fun _ => (1:ℝ))
    (fun j w => ∀ i, StepStages j i → ∃ μ : ℝ, 0 < μ ∧ cash (Testing.query p K j i) (D.L j) w μ)
    (fun j => eventually_transitions j atTop _ (h j))
  refine ⟨k,hk,h₁,fun w hw => ?_⟩
  have he j i : ∃ μ : ℝ, 0 < μ ∧ (StepStages j i → cash (Testing.query p K j i) (D.L j) (w j i) μ) := by
    by_cases ha : StepStages j i
    · obtain ⟨x,hx,hq⟩ := hK j _ (hw j i) i ha; exact ⟨x,hx,fun _ => hq⟩
    exact ⟨1,zero_lt_one,fun u => False.elim (ha u)⟩
  choose u hu hU using he
  let μ := rateLo (fromMin u)
  have hp j : ∀ᶠ x in atTop, ∀ i, StepStages j i → Teller.live (Testing.query p K j i) (D.L j) (w j i)
      (fun S T _ A y U k V => μ j*(fiery G y (D.L j))^2 * A.shares ≤ A.assessed T y U (S.prediction U k) V) x := by
    apply eventually_transitions
    intro i ht
    have hg := (hU j i ht).late
    have hm : μ j ≤ u j i := (rateLo_le _ j).trans (fromMin_le u ht)
    filter_upwards [hg] with x hx c f S hl hs T hb F A Q k V ha he
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (sq_nonneg _)) (Nat.cast_nonneg _)).trans
      (hx c f S hl hs T hb F A Q k V ha he)
  obtain ⟨F,hF,hf,H⟩ := collect_upper (fun _ => (1:ℝ)) _ hp
  exact ⟨F,μ,fun j i => lt_of_lt_of_le zero_lt_one ((h₁ j).trans (hw j i)),hF,hf,
    rateLo_pos fun j => lt_min (hu j j) (hu j (j-1)), rateLo_anti _, fun j i h x he => H j x he i h⟩

/-- In particular, nonempty choice even with extra w-asks per pair.
Can (but needn't) make w a monotone-staged price on real edges. Allow
non-edges arbitrary high w-asks too. -/
theorem charges_extra (h : ∀ j i, StepStages j i → PressureGate p K j i (D.L j)) (x : ℕ → ℕ → ℝ) :
    ∃ w e μ f, Charges K D w e μ ∧ x ≤ w ∧ Monotone f ∧ ∀ j i, StepStages j i → w j i = f j := by
  obtain ⟨k,-,-,H⟩ := charges h
  let v (j) := max (k j) (fromMax x j)
  let w (j i) := max (prefixHi v j) (x j i)
  obtain ⟨e,μ,hW⟩ := H w fun _ _ =>
    (le_max_left ..).trans ((le_prefixHi v le_rfl).trans (le_max_left ..))
  exact ⟨w,e,μ,prefixHi v,hW,fun _ _ => le_max_right ..,prefixHi_mono _,fun j i ha =>
    max_eq_left (((le_fromMax x ha).trans (le_max_right ..)).trans (le_prefixHi v le_rfl))⟩

variable {w : ℕ → ℕ → ℝ} {F μ : ℕ → ℝ} (h : Charges K D w F μ)
include h



/-- Spend it for any eligible Tube on **this** schedule. Premises include
Funds, especially the kernel & path estimates (and Plot/Slice still required
in the conclusion). No assuming a Directed object just to charge this price. -/
theorem Charges.ticket {T : Protection D} {W : Delays T} (he : F ≤ W.betaEntry)
    {Y : Bar W} {I : Wait Y} {a : Levels G} (ha : Paid I a) (m P : ℕ) (R : Tube G (a.clock.op m P))
    (hx : Teller.Funds (Testing.query p K (a.clock.J (m+1)) (a.clock.J m)) _ R) :
    let j := a.clock.J (m+1); let S := a.clock.op m P
    ∀ (A : Stores S) (U : Config G _) (k : S.Choices) (V : Config G _) (X : Forest S.ratio),
      Stores.SliceSet S X U → Stores.Plot A U k V (a.clock.hatBeta m) (w j (a.clock.J m)) →
        μ j * (a.clock.threshold (m+1))^2 * A.shares ≤ A.assessed R (a.clock.hatBeta m) U (S.prediction U k) V := by
  intro j S A U k V X hs hg
  have hl : S.patch.L = D.L j := block_eq ha m
  have hc : 100*(1+radiusB (a.clock.hatBeta m)) ≤ (a.S.side m P).val := by
    rw [add_comm 1]; exact a.fits.sizeT m P
  have hp := h.earn j (a.clock.J m) (step_paid a m) (a.clock.hatBeta m) ((he j).trans (ha.pays m))
    _ _ S hl hc R hx X A U k V hs hg
  change μ j * (temp (a.clock.hatBeta (m+1)))^2 * A.shares ≤ _
  rw [beta_eq ha]
  exact hp
end
end YM.Push.PriceCompiler
