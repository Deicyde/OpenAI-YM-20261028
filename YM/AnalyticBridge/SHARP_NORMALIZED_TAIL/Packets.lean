import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Cancellation
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Playback
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Wisps
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Protected


/-!
# Procurement under the annulus criterion

No assumption on the integral of the *charged* coefficient. Need the
indicated L¹ cost on ANCILLARY factors (not hiding them; include all those
compensations/extensions even on sectors with holes!) and concrete applicability
of the sampled annulus ledger for each packet, including all rotations. Can
verify pointwise on its protections; we need only this on nonzero ancillary
multiplier. Projection then permits the same estimate under every assembly
of these factors on the prescribed support reads.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp
open Filter Function Lattice RG Pressure Pressure.Stores Wilson Tree MeasureTheory Matrix
open Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Gaussian SectorNext.Vacuum.ReLog
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented Finset Inventory
open Precision SectorNext.Remainder SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius YM.Push.SectorMeasure

variable {c f : Side} {G : Gauge} {x W : ℝ} {S : StepData c f}
  {T : Tube G S} {R : Rep G f} {D : Allocation G S x W} {F : Forest S.ratio}
  {L : Almanac T D R F} {V : Config G c} {E ι : Type} [DecidableEq E] {K : Cards S ι E}
  {H : Roster L V K}

/-- STEM recipe. The rest of the integrand is *also* tracked as `more`.
`a` may be supplied by a physical log for all links where used; has real
prerequisite `Ensures` on those windows. The coefficient at the sample
can't be computed by another covariance lottery and then used as-is:
`Roster` and `Contracts.script` require actual matching. -/
structure Staple (H : Roster L V K) (θ : ℝ) (α : ℕ) where
  stems : ι → Finset (Stores S)
  partition i : (stems i).biUnion items=items (K.seeds i)
  spread i : ((stems i : Finset _) : Set (Stores S)).PairwiseDisjoint items
  active i s : s∈stems i → 0 < s.shares
  outer : ι → Stores S → S.Choices → Signed → Affine.Window S
  booked : ι → Stores S → S.Choices → Signed → Affine.Window S
  a : (i : ι) → S.Choices → Room G x F (H.sample i) → Signed → RG.Directions G f
  more : (i : ι) → S.Choices → Room G x F (H.sample i) → ℝ
  uses i O (k : S.Choices) y : O∈stems i → more i k y≠0 → ∀ s, Ensures
    (L.texture V (H.sample i) k y) V O (outer i O k) (booked i O k)
    x k (a i k y) W θ α F (H.sample i) s

-- Currency maps. `leave` includes half the rate of `Affine.remaining`.
def intensity (G : Gauge) (L : Side) (x κ : ℝ) := κ/8*(Scales.p G L x)^2


def kept (K : Cards S ι E) (G : Gauge) (x κ : ℝ) (v : ι → ℝ) i :=
    v i * Real.exp (-(2*intensity G S.patch.L x κ)*(K.seeds i).shares)
def leave (K : Cards S ι E) (G : Gauge) (x κ : ℝ) (v : ι → ℝ) (w : E → ℝ) i :=
    v i * Real.exp (-intensity G S.patch.L x κ*(K.seeds i).shares) * ∏ t∈K.marks i, w t

lemma uses_price (K : Cards S ι E) (G : Gauge) (x κ : ℝ) (v : ι → ℝ) (w : E → ℝ) i :
    let r := Inventory.bill S (intensity G S.patch.L x κ) w
    kept K G x κ v i * (∏ t∈ K.claims.tokens i, r t) = leave K G x κ v w i := by
  intro r
  unfold r
  rw [show K.claims.tokens i = request (K.seeds i) (K.marks i) from rfl,charges]
  unfold kept leave
  rw [← mul_assoc (v i * _) _ _,mul_assoc (v i) _ _,← Real.exp_add]; ring_nf

variable [Fintype E]
lemma kept_sums (K : Cards S ι E) {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) (G : Gauge) (x κ : ℝ)
    {l : Grid (Site c)} (w : E → ℝ) {a δ : ℝ} (h : Sufficient K.X l (leave K G x κ v w) a δ) (hw : ∀ t,0 < w t) :
    Summable (kept K G x κ v) := by
  refine unweight (K.claims.tokens) (ρ:=Inventory.bill S (intensity G S.patch.L x κ) w) (supplied_sum K.full h)
    (fun t => Sum.rec (fun _ => Real.exp_pos _) (fun i => hw i) t) (fun i => ?_)
  rw [abs_of_nonneg (show 0 ≤ kept K G x κ v i from mul_nonneg (hv i) (Real.exp_pos _).le), uses_price]

namespace Staple
variable {θ : ℝ} {α : ℕ} (N : Staple H θ α)
  {P : Teller G} {κ eps : ℝ} {n : ℕ}

lemma specs i : ∑ O∈N.stems i,O.shares=(K.seeds i).shares := by
  simp_rw [← card_items,← N.partition i,card_biUnion (N.spread i)]

def heat (i : ι) (O : Stores S) (k : S.Choices) (y : Room G x F (H.sample i)) := vital R.beta x
    (L.texture V (H.sample i) k y) V O (N.outer i O k) (N.booked i O k) T k (N.a i k y)
lemma heat_pos (i : ι) O k y : 0 < N.heat i O k y := Real.exp_pos _

/-- Additional price inputs. Purchase before evaluating trigger sums etc.
Uniform every k (likelihood also supplied by the atlas, never presumed paid
for free). No proof of these estimates from just `Lawful`. -/
structure Contracts (ψ : H.Script) (eps : ℝ) (n : ℕ) (v : ι → ℝ) : Prop where
  prim : H.uniform ψ
  enough : ∀ i, 0 ≤ v i
  registered i k : Measurable (ψ i k)
  script i k y : ψ i k (H.primary i y)=N.more i k y * ∏ O∈N.stems i, N.heat i O k y
  extra i k : Integrable (N.more i k) (L.climate V (H.sample i) k)
  price i k : (∫ y, ‖N.more i k y‖ ∂(L.climate V (H.sample i) k)) ≤
    v i * Real.exp (valuation (K.seeds i) eps n x G)

/-- Local affine-subtracted payment pointwise at the completion (so it
lives on the actual nonabelian group and the protection used here). -/
lemma heat_bought (a : Ledger P S.patch.L W κ θ eps n α x) (h : P.Funds S T)
    (hh : PointCharge T x W κ) (hx : 100*(1+radiusB x) ≤ c.val)
    (hb : R.beta ∈ Set.Icc (Scales.y G S.patch.L x/2) (2*Scales.y G S.patch.L x))
    (i k y) (hg : N.more i k y≠0) (O : Stores S) (hO : O∈N.stems i) :
    N.heat i O k y ≤ Real.exp (-(2*intensity G S.patch.L x κ)*O.shares - valuation O eps n x G) := by
  apply (used (L.texture V (H.sample i) k y) V _ _ _ k _ F _ (show S.patch.L=S.patch.L from rfl) hx h
    R.beta θ eps W κ α n hh a hb (fun i hi => F.on_tree _ ⟨i,hi⟩) (N.uses i O k y hO hg)).2.trans_eq
  unfold valuation intensity; ring_nf

/-- Aggregate within a component before buying any tag marginals. Only
use the multiplier estimate on its nonvanishing domain. Generic on the
real `Script` for later reuse with clipped-energy valuations as well. -/
theorem sample_purchase (i : ι) (v : ℝ) (_hv : 0≤v) (u b : ℝ)
    (P : S.Choices → H.point i → ℝ) (a : L.Available V) (k : S.Choices)
    (hp : Measurable (P k))
    (q : Stores S → Room G x F (H.sample i) → ℝ)
    (M : Room G x F (H.sample i) → ℝ)
    (hm : Integrable M (L.climate V (H.sample i) k))
    (h : ∀ y, P k (H.primary i y)= M y * ∏ O∈N.stems i, q O y)
    (hq : ∀ y, M y≠0 → ∀ O∈N.stems i, ‖q O y‖ ≤ Real.exp ((-u-b)*O.shares))
    (hB : (∫ y,‖M y‖ ∂L.climate V (H.sample i) k) ≤ v * Real.exp (b*(K.seeds i).shares)) :
    Integrable (P k) (H.paper i k) ∧ (∫ y, ‖P k y‖ ∂ H.paper i k) ≤
      v * Real.exp (-u*(K.seeds i).shares) := by
  let T := L.climate V (H.sample i) k
  let φ y := P k (H.primary i y)
  have hf := H.measured a i k
  let g : ℝ := (K.seeds i).shares
  let r := Real.exp ((-u-b)*g)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hh y : ‖φ y‖ ≤ ‖M y‖*r := by
    unfold φ; rw [h, norm_mul]
    by_cases he : M y=0
    · simp [he]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_prod]
    apply (prod_le_prod (fun i _ => norm_nonneg _) (hq y he)).trans_eq
    unfold r g; rw [← N.specs, Nat.cast_sum, Finset.mul_sum]; exact (Real.exp_sum ..).symm
  have hmeas : Measurable φ := hp.comp hf.measurable
  have he : Integrable φ T := (hm.norm.mul_const r).mono' hmeas.aestronglyMeasurable (Eventually.of_forall hh)
  refine ⟨(hf.integrable_comp hp.aestronglyMeasurable).mp he,?_⟩
  rw [← hf.map_eq, integral_map hf.measurable.aemeasurable hp.norm.aestronglyMeasurable]
  calc
    _ ≤ ∫ y, ‖M y‖*r ∂T := integral_mono he.norm (hm.norm.mul_const _) hh
    _ ≤ v * Real.exp (b*g)*r := by rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right hB hr
    _ = _ := by unfold r g; rw [mul_assoc,← Real.exp_add]; ring_nf

/-- The L¹ currency to buy `assembled`. Annulus supplies valuations for
overhead and a second genuine seed rate; only half of that seed exponent
is tested in `leave`, saving half to consume requests from every slot. -/
theorem purchase (hh : P.Funds S T) (hx : 100*(1+radiusB x) ≤ c.val) (ha : L.Available V)
    (a : Ledger P S.patch.L W κ θ eps n α x) (hp : PointCharge T x W κ)
    (hb : R.beta ∈ Set.Icc (Scales.y G S.patch.L x / 2) (2*Scales.y G S.patch.L x))
    (ψ : H.Script) {v : ι → ℝ} (h : N.Contracts ψ eps n v)
    {w : E → ℝ} (hw : ∀ i,0 < w i)
    {s δ : ℝ} {C : Grid (Site c)} (ht : Sufficient K.X C (leave K G x κ v w) s δ) :
    H.LetterBudget ψ (kept K G x κ v) := by
  have hz i k := N.sample_purchase i (v i) (h.enough i) (2*intensity G S.patch.L x κ) (coin G S.patch.L eps n x)
    (ψ i) ha k (h.registered i k) (fun O => N.heat i O k) (N.more i k) (h.extra i k) (h.script i k)
    (fun y hg O hO => by
      rw [Real.norm_of_nonneg (N.heat_pos i O k y).le]; exact (N.heat_bought a hh hp hx hb i k y hg O hO).trans_eq (by
        unfold valuation; ring_nf)) (h.price i k)
  exact ⟨h.prim,fun i => mul_nonneg (h.enough i) (Real.exp_pos _).le,
    kept_sums K h.enough G x κ w ht hw,fun i k => (hz i k).1,fun i k => (hz i k).2⟩
end Staple
end YM.AnalyticBridge.Sharp
