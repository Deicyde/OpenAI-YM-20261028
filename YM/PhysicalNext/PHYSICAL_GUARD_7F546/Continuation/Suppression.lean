import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Stencil
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Moment
import YM.Push.PRICE_COMPILER.Post

/-!
# Probability cost of removing the central guards (held data)

Can keep just the old Receipt from the *actual* clouds. No product of
independent reads. On the actual target marginal, buy exp(r ∑ zᵢ²)
over the whole watch area (not many separate inspections). Even though
r may be as small as inverse polynomial in radiusB, this still pays
arbitrary inverse-power laws of x against the meter at fixed L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Rows Tree Push.SectorMeasure MomentBound
open Extra.Iteration Extra.Iteration.Scales YM.AnalyticBridge.LocalGaussianLaws Remote Local
open MeasureTheory SectorTools.PhysicalGaussianSwitch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}
lemma reserve_upper (K : ℕ) {U : ℝ} (hu : 0 ≤ U) :
    K * (reservation K U * U) ≤ 1 := by
  unfold reservation
  have he : 0 < 1 + K * U := by positivity
  have hp := (zero_lt_one.trans_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg K) hu)) :
    0 < 1 + K * U)
  field_simp
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) K) hu]

private def energy {I : Type} [Fintype I] (r : ℝ) (z : Gaussian.Vec I) := Real.exp (r * ∑ i,z i^2)

open Primitives.GCC Multi.Vacuum.Gauss in
lemma pay_guard {I : Type} [Fintype I] [DecidableEq I]
    {C : Gaussian.Table I} {K : ℕ} {U : ℝ} (h : C.PosSemidef)
    (hC : Fintype.card I ≤ K) (hu : 1 ≤ U) (hp : ∀ i j, |C i j| ≤ U) :
    let r := reservation K U
    Integrable (energy (I:=I) r) (Gaussian.cloud C) ∧
    (∫ z, energy r z ∂Gaussian.cloud C) ≤ Real.exp 2 := by
  intro r
  let w : Unit → Gaussian.Vec I := fun _ _ => r; let t : Finset Unit := {()}
  have hu0 := zero_le_one.trans hu
  have hK := reservation_pos K hu0
  have hh : (Fintype.card I:ℝ) ≤ K := Nat.cast_le.mpr hC
  let A := Common.cable (V:=Unit) C
  have hP : Common.pool t C w := by
    apply Common.scaled C ((K:ℝ)*U) (by positivity)
    · intro i; exact (sum_le_sum (g:=fun _ => U) (fun j _ => hp i j)).trans
        (by simpa only [sum_const,card_univ,nsmul_eq_mul] using mul_le_mul_of_nonneg_right hh hu0)
    · exact fun i hi j => hK.le
    intro a; rw [sum_singleton]; exact le_rfl
  have hq := Moment.amount (Common.pool_enough C h hP); unfold Moment.sumCharge at hq
  have HM : Moment.due t A w ≤ 1 := by
    unfold A; rw [Common.common_due C h]; dsimp only [t, w]; rw [sum_singleton]
    calc
      _ ≤ ∑ _i : I, r * U := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hp _ _)) hK.le
      _ ≤ K * (reservation K U * U) := Eq.trans_le (by rw [sum_const,card_univ,nsmul_eq_mul])
        (mul_le_mul_of_nonneg_right hh (mul_nonneg hK.le hu0))
      _ ≤ _ := reserve_upper K hu0
  let B := energy (I:=I) r
  have he (z) : Real.exp (∑ i∈t,pay (w i) (mapRows (A i) z)) = B (mapRows (A ()) z) := by
    simp only [t,sum_singleton]; unfold B energy; rw [mul_sum]; rfl
  change Integrable (fun z => Real.exp (∑ i∈t,pay (w i) (mapRows (A i) z))) _ ∧
    (∫ z, Real.exp (∑ i∈t,pay (w i) (mapRows (A i) z)) ∂_) ≤ _ at hq
  simp_rw [he] at hq
  have hl : Continuous B := by unfold B energy; fun_prop
  obtain ⟨ht,hx⟩ := pay_pull (Common.paid_one C) B hl.aestronglyMeasurable
  exact ⟨ht.mp hq.1,hx.symm.trans_le (hq.2.trans (Real.exp_monotone (show 2*Moment.due t A w ≤ 2 by linarith)))⟩

section report
variable {m : Type*} {F : Forest S.ratio} {x β : ℝ} {A : Stores S}
def away (W : Finset (Bond f)) (r : ℝ) := {Z : Gaussian.Vec (In x A F (G:=G)) | ¬ Guards W Z r}

def trimmed (W : Finset (Bond f)) (r : ℝ) := {z : Gaussian.Vec (SlotsW A F x W G) |
    ¬∀ i : Window A F x W, ‖tape z i‖ ≤ r}

lemma trim_meas (W : Finset (Bond f)) (r : ℝ) : MeasurableSet (trimmed (A:=A) (F:=F) (x:=x) (G:=G) W r) := by
  unfold trimmed
  change MeasurableSet {z : Gaussian.Vec (SlotsW A F x W G) | ∀ i : Window A F x W, ‖tape z i‖ ≤ r}ᶜ
  simp only [Set.setOf_forall]
  exact (MeasurableSet.iInter fun i => measurableSet_le
    (((measurable_pi_apply i).comp tape.measurable).norm) measurable_const).compl
lemma away_preimage (W : Finset (Bond f)) (r : ℝ) :
    away (A:=A) (F:=F) (x:=x) (G:=G) W r =
    (fun Z : Gaussian.Vec (In x A F (G:=G)) => Z ∘ accessing A F x W G) ⁻¹' trimmed W r := rfl
lemma away_meas (W : Finset (Bond f)) (r : ℝ) : MeasurableSet (away (A:=A) (F:=F) (x:=x) (G:=G) W r) := by
  rw [away_preimage]; refine trim_meas .. |>.preimage ?_; unfold Function.comp; fun_prop

private lemma generic_trim {I : Type} [Fintype I] [DecidableEq I] {C : Gaussian.Table (I × G.ColorIndex)}
    (hC : C.PosSemidef) {K : ℕ} {U t : ℝ} (hu : 1 ≤ U) (hK : Fintype.card (I×G.ColorIndex) ≤ K) (ht : 0≤t)
    (hp : ∀ i j,|C i j| ≤ U)
    (M : Set (Gaussian.Vec (I × G.ColorIndex))) (hM : MeasurableSet M) (hr' : ∀ z ∈ M, ¬∀ i, ‖tape z i‖ ≤ t) :
    (Gaussian.cloud C).real M ≤ Real.exp 2 * Real.exp (-reservation K U * t^2) := by
  let r:=reservation K U; have hr : 0<r := reservation_pos K (zero_le_one.trans hu)
  obtain ⟨hI,H⟩ := pay_guard hC hK hu hp
  rw [neg_mul, Real.exp_neg,← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  let μ:= Gaussian.cloud C
  let y:= Real.exp (r*t^2)
  calc
    μ.real M * y = ∫ _z in M,y ∂μ := by rw [setIntegral_const]; rfl
    _ ≤ ∫ z in M, energy r z ∂μ := by
      refine setIntegral_mono_on (integrable_const _) hI.integrableOn hM (fun z hz => Real.exp_monotone ?_)
      have hz := hr' z hz
      simp only [not_forall,not_le] at hz
      obtain ⟨i,hi⟩ := hz
      have he := price_square z
      rw [dotProduct] at he -- dotProduct def
      simp_rw [← sq] at he
      apply mul_le_mul_of_nonneg_left _ hr.le
      rw [he]
      exact (pow_le_pow_left₀ ht hi.le 2).trans (single_le_sum (f:=fun u : I => ‖tape z u‖^2) (fun _ _ => sq_nonneg _) (mem_univ i))
    _ ≤ ∫ z, energy r z ∂μ := setIntegral_le_integral hI (Eventually.of_forall fun z => Real.exp_nonneg _)
    _ ≤ _ := H

/-- At the price of that real reservation. -/
lemma reserve_away (W : Finset (Bond f)) (t : ℝ) (ht : 0≤t) {U : ℝ} {K : ℕ} (hu : 1≤U)
    (hK : Fintype.card (SlotsW A F x W G) ≤ K)
    {Q : Gaussian.Table (In x A F (G:=G))} (hQ : Q.PosSemidef) (e : SlotsW A F x W G ↪ In x A F (G:=G))
    (he : e=accessing A F x W G) (hp : ∀ i j, |Q (e i) (e j)| ≤ U) :
    (Gaussian.cloud Q).real (away W t) ≤ Real.exp 2 * Real.exp (-reservation K U * t^2) := by
  subst e
  let e := accessing A F x W G
  let C:=Q.submatrix e e; let M:=trimmed (A:=A) (F:=F) (x:=x) (G:=G) W t
  have hE := AnalyticBridge.GaussianFieldAlignment.Completed.marginal e hQ
  have hM : MeasurableSet M := trim_meas ..
  have hC : C.PosSemidef := hQ.submatrix _
  have hl : (Gaussian.cloud Q).real (away W t) = (Gaussian.cloud C).real M := by
    rw [away_preimage]; exact congr_arg ENNReal.toReal (hE.measure_preimage hM.nullMeasurableSet)
  rw [hl]
  exact generic_trim hC hu hK ht hp M hM (fun z hz => hz)
end report









-- moment and error bills from WeightedAt, now even with K-ceiling variable




end YM.PhysicalNext.PhysicalGuard7f546.Curved
