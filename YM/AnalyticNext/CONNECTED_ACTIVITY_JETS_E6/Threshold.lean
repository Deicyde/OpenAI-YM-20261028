import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Colony

/-!
# Small activities and second tree thresholds
Uniform Summation at μ output. Extract complete D. Allows optional k-order
polynomial on BOTH species. Further degree k tail verses. All explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {V : Finset (Molecule S)} {b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
namespace Cash
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (hk : X.x=α) (he : X.width=o.K)

lemma gross (m k r : ℕ) (t : ℝ) {q : ℝ} (hq : q ≤ Q.exp) : Ac.Hit H.largeAt (radiusB α)
    (fun p => H.ours m k r t p.val) q (H.faresP.ceiling m k r t) := by
  intro p
  have hx:= budget_pull (fun i : H.ThickP=> i.val) (Subtype.val_injective) (H.charged m k r t p)
  refine budget_mono hx (fun p=>?_) fun i=> ?_
  · split
    next h => exact mul_nonneg (H.ours_pos ..) (Real.exp_pos _).le
    exact le_rfl
  split
  next hi => dsimp only; rw [if_pos (show p∈ H.unionP i.val from hi)]; apply mul_le_mul_of_nonneg_left _ (H.ours_pos ..); apply Real.exp_monotone
             exact mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg _)
  next hz => exact hx.1 i
lemma goods (m k r : ℕ) (t : ℝ) {q : ℝ} (hq : q≤ Q.exp) : Ac.Hit H.smallAt (radiusB α)
    (fun p=> H.ours m k r t p.val) q (H.faresP.ceiling m k r t) := by
  intro p
  have hx := budget_pull (fun i:H.ThinP => i.val) Subtype.val_injective (H.charged m k r t p)
  refine budget_mono hx (fun p=>?_) fun i=> ?_
  · split
    next h=> exact mul_nonneg (H.ours_pos ..) (Real.exp_pos _).le
    exact le_rfl
  split
  next hi => dsimp only; rw [if_pos (show p∈ H.unionP i.val from hi)]; apply mul_le_mul_of_nonneg_left _ (H.ours_pos ..); apply Real.exp_monotone
             exact mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg _)
  next hz => exact hx.1 i

def thinPay (k : ℕ) (i : H.ThinP) := H.ours 0 k 0 0 i.val
def broadPay (k : ℕ) (i : H.ThickP) := H.ours 0 k 1 0 i.val

include hk he
lemma coinPay (k : ℕ) : (∀ i:H.ThinP, ‖H.entries X i‖*(1+H.shapeW i.val)^k ≤ H.thinPay k i) ∧
    (∀ i:H.ThickP, ‖H.deposits X i‖*(1+H.shapeW i.val)^k ≤ H.broadPay k i) := ⟨fun i=> H.anyF X hk he i.val k,
    fun i=> H.pick X hk he 0 k 1 i.val (Nat.zero_le _) (forced_cost i.val i.2.2) 0 (H.positive_volume i.val)⟩
lemma errorPaid (k : ℕ) : (∀ i,‖H.entries X i‖ ≤ H.thinPay k i) ∧ ∀ i,‖H.deposits X i‖ ≤ H.broadPay k i := by
  have h i : 1 ≤ (1+H.shapeW i)^k := one_le_pow₀ (le_add_of_nonneg_right (H.positive_volume i))
  exact ⟨fun i => (le_mul_of_one_le_right (norm_nonneg _) (h _)).trans ((H.coinPay X hk he k).1 i), fun i=>
    (le_mul_of_one_le_right (norm_nonneg _) (h _)).trans ((H.coinPay X hk he k).2 i)⟩
end Cash
namespace Target
variable (Q : YM.ConnectedActivityE6.Target G P)

def quantum (L : Side) (μ x : ℝ) (m k r : ℕ) (t : ℝ) := (Q.costs L μ 1 x 0).ceiling m k r t
def mark (L : Side) (μ x : ℝ) := (Q.costs L μ 1 x 0).markSeed
lemma quantum_form (L : Side) (μ x : ℝ) (m k r : ℕ) (t : ℝ) : Q.quantum L μ x m k r t =
    Q.quantum L μ x m k 0 t * Real.exp (-Q.mark L μ x*r) := by
  unfold quantum mark Mixed.Costs.ceiling Reserves.extract; simp only [Nat.cast_zero,mul_zero,sub_zero,neg_mul]
  rw [sub_eq_add_neg, Real.exp_add]; ring

def overture (L : Side) (μ x : ℝ) (k : ℕ) := Q.quantum L μ x 0 k 0 0

def mergeScale (L : Side) (μ x : ℝ) (k : ℕ) := 20*Q.overture L μ x k

lemma tempo (L : Side) {μ : ℝ} (h : 0 < μ) (k : ℕ) : Rate G L Q.rate (fun x => Q.mergeScale L μ x k) :=
    (Q.rate_none L h 0 k 0).mul_left _

lemma overture_pos {μ : ℝ} (x : ℝ) (k : ℕ) (hr : 0 < betaF G x L) : 0 < Q.overture L μ x k := by
  let b:= Q.costs L μ 1 x 0
  have he : 0 < b.rootHit := by dsimp only [b,Target.costs,Buy.quote,goal]; positivity
  have hp := Q.usable
  unfold overture quantum Mixed.Costs.ceiling Reserves.extract Reserves.polyPrice Reserves.treeYield
  dsimp only [Target.costs,Buy.quote] at *; unfold b at *; change 0 < _ * ((_ * (1 / 2) ^ (0:ℕ))*_)
  simp only [pow_zero,mul_one]
  have hz : 0 < (1-1 / (2:ℝ))⁻¹ := by norm_num
  exact mul_pos (mul_pos (mul_pos (by positivity) (Real.exp_pos _)) (Real.exp_pos _)) (mul_pos he hz)

lemma certify (L : Side) {μ : ℝ} (h : 0<μ) (k : ℕ) (a b : ℝ) (_ha : 0<a) (_hb : 0<b) : ∀ᶠ x : ℝ in atTop,
    let u:=Q.overture L μ x k; let v:=Q.mergeScale L μ x k
    let B:=radiusB x
    0<u ∧ u≤v ∧ v≤1/2 ∧ degreePrice B u a≤1/2 ∧ degreePrice B v b ≤ 1/2 := by
  have hx : Rate G L 0 (fun x=> (Animals.ballCost (radiusB x):ℝ)) := by
    have he := Census.width_rate G L 1 0; simpa only [one_mul,add_zero] using! he
  have he (F : ℝ → ℝ) (q) (hp : Rate G L Q.rate F) : ∀ᶠ x in atTop,
    |degreePrice (radiusB x) (F x) q| ≤ 1/2 := by
    apply Rate.below (G:=G) (L:=L) (a:=0+Q.rate) ?_ (by rw [zero_add]; exact Q.stop) (1/2) (by norm_num)
    unfold degreePrice Trees.stretch; simp_rw [div_eq_mul_inv]; exact (((hx.mul hp).mul_right _).mul_left _)
  have hs := Q.tempo L h k
  filter_upwards [hs.below Q.stop _ (show (0:ℝ)<1/2 by norm_num),Delay.shift_pos G L,
    he _ a (Q.rate_none L h 0 k 0), he _ b hs] with x hX hv hx hz u v B
  have hu := Q.overture_pos (L:=L) (μ:=μ) x k hv
  exact ⟨hu,(by change u ≤ 20*u; change 0 < u at hu; linarith),(le_abs_self _).trans hX,
    (le_abs_self (degreePrice B u a)).trans hx,(le_abs_self _).trans hz⟩
end Target
end YM.ConnectedActivityE6
