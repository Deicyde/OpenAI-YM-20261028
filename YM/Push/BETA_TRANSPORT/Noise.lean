import YM.Next.FLUCTUATIONS.Sector
import YM.Push.BETA_TRANSPORT.Gibbs

/-!
# The actual penaltyZ, joint bond noise and shared tags at a single step

S (including every predictor, frame and discrete tag choice law) held fixed. Product
noise is conditionally independent *given* the predicted field; `tagWeight` multiplies
by ONE joint tag likelihood on the whole array. Real differentiation, including at 0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG Pressure Gibbs MeasureTheory Filter Set
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {c f : Side} (S : StepData c f) {G : Gauge}

def linkEnergy (v : G.El) := S.kernel.penalty * G.price v
def linkCap := S.kernel.penalty * 2
lemma link_estimate : EnergyEstimate (linkEnergy (G:=G) S) (linkCap S) :=
  ⟨measurable_const.mul G.continuous_price.measurable,
    fun x => mul_nonneg S.kernel.penalty_pos.le (G.price_range x).1,
    fun x => mul_le_mul_of_nonneg_left (G.price_range x).2 S.kernel.penalty_pos.le,
    mul_nonneg S.kernel.penalty_pos.le zero_le_two⟩
lemma link_factor (β : ℝ) : S.penaltyWeight (G:=G) β = factor (linkEnergy S) β := by
  ext x; simp only [StepData.penaltyWeight,linkEnergy,factor,mul_assoc]
lemma link_Z (G : Gauge) (β : ℝ) : S.penaltyZ β G = Z G.probHaar (linkEnergy S) β := by
  simp [Z,StepData.penaltyZ,link_factor]

lemma penaltyZ_hasDerivAt (G : Gauge) (β : ℝ) : HasDerivAt (S.penaltyZ · G)
    (- mean G.probHaar (linkEnergy S) β * S.penaltyZ β G) β := by
  simp_rw [link_Z]; exact (link_estimate S).Z_hasDerivAt β
@[simp] lemma penaltyZ_zero (G : Gauge) : S.penaltyZ 0 G = 1 := by rw [link_Z,Z_zero]
@[fun_prop] lemma penaltyZ_cont (G : Gauge) : Continuous (S.penaltyZ · G) :=
  continuous_iff_continuousAt.mpr fun β => (penaltyZ_hasDerivAt S G β).continuousAt

def noiseEnergy (Q V : Config G c) := ∑ b : Bond c, linkEnergy S (V b * (Q b)⁻¹)
def noiseCap := (Fintype.card (Bond c) : ℝ) * linkCap S
def noiseMean (G : Gauge) (β : ℝ) :=
  (Fintype.card (Bond c) : ℝ) * mean G.probHaar (linkEnergy S) β
def noiseCost (R : ℝ) := cost (noiseCap S) R * cost (noiseCap S) R
lemma noiseCost_pos (R : ℝ) : 0 < noiseCost S R := mul_pos (cost_pos ..) (cost_pos ..)
lemma noiseCap_nonneg : 0 ≤ noiseCap S := by unfold noiseCap linkCap; have := S.kernel.penalty_pos; positivity

@[fun_prop] lemma noiseEnergy_cont : Continuous (fun p : Config G c × Config G c => noiseEnergy S p.1 p.2) := by
  unfold noiseEnergy linkEnergy; fun_prop
lemma energy_estimate (Q : Config G c) : EnergyEstimate (noiseEnergy S Q) (noiseCap S) := by
  refine ⟨((noiseEnergy_cont S).comp (continuous_const.prodMk continuous_id)).measurable,
    fun V => Finset.sum_nonneg (fun _ _ => (link_estimate S).nonneg _),fun V => ?_,noiseCap_nonneg S⟩
  simpa [noiseEnergy,noiseCap] using (Finset.sum_le_sum (s:=Finset.univ)
    (fun b _ => (link_estimate S).bound (V b * (Q b)⁻¹)))
lemma noise_factor (β : ℝ) (Q V : Config G c) :
    S.noise β Q V = Next.Fluctuations.Sector.prefactor S G β * factor (noiseEnergy S Q) β V := by
  unfold StepData.noise Next.Fluctuations.Sector.prefactor factor noiseEnergy
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ, Finset.mul_sum, Real.exp_sum,
    link_factor,factor]
lemma noise_Z (β : ℝ) (Q : Config G c) :
    Z (prior G c) (noiseEnergy S Q) β = (S.penaltyZ β G) ^ Fintype.card (Bond c) := by
  have he := S.noise_mass β Q
  simp_rw [noise_factor, integral_const_mul] at he
  rw [Next.Fluctuations.Sector.prefactor,inv_pow,← Z] at he
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ (S.penaltyZ_pos β).ne'))
    (he.trans (inv_mul_cancel₀ (pow_ne_zero _ (S.penaltyZ_pos β).ne')).symm)
lemma noise_mean (β : ℝ) (Q : Config G c) : mean (prior G c) (noiseEnergy S Q) β = noiseMean S G β := by
  let n := Fintype.card (Bond c)
  let z := S.penaltyZ β G
  let e := mean G.probHaar (linkEnergy S) β
  have he : (n:ℝ) * z^(n-1) * (-(e)*z) = -(n*e)*z^n := by
    cases n with
    | zero => simp
    | succ k => rw [Nat.add_one_sub_one, pow_succ]; ring
  have hp := ((penaltyZ_hasDerivAt S G β).pow n)
  have h := (energy_estimate S Q).Z_hasDerivAt (μ:=prior G c) β
  simp_rw [show Z (prior G c) (noiseEnergy S Q) = (S.penaltyZ · G)^n from funext fun b => noise_Z S b Q] at h
  exact neg_injective (mul_right_cancel₀ (pow_ne_zero n (S.penaltyZ_pos β).ne') ((h.unique hp).trans he))
lemma noise_tilt (β : ℝ) (Q : Config G c) : S.noise β Q = tilt (prior G c) (noiseEnergy S Q) β := by
  ext x; simp only [noise_factor,tilt,noise_Z, Next.Fluctuations.Sector.prefactor,inv_pow]
lemma noise_bounds {β R : ℝ} (hβ : |β| ≤ R) (Q V : Config G c) :
    (noiseCost S R)⁻¹ ≤ S.noise β Q V ∧ S.noise β Q V ≤ noiseCost S R := by
  rw [noise_tilt]; exact (energy_estimate S Q).tilt_bounds hβ V
lemma noise_pos (β : ℝ) (Q V : Config G c) : 0 < S.noise β Q V := by
  rw [noise_tilt]; exact (energy_estimate S Q).tilt_pos ..
lemma noiseMean_bound (β : ℝ) : 0 ≤ noiseMean S G β ∧ noiseMean S G β ≤ noiseCap S :=
  ⟨mul_nonneg (Nat.cast_nonneg _) ((link_estimate S).mean_bound β).1,
    mul_le_mul_of_nonneg_left ((link_estimate S).mean_bound β).2 (Nat.cast_nonneg _)⟩
lemma noise_hasDerivAt (Q V : Config G c) (β : ℝ) : HasDerivAt (S.noise · Q V)
    (S.noise β Q V * (noiseMean S G β - noiseEnergy S Q V)) β := by
  simp_rw [noise_tilt,← noise_mean S β Q]
  exact (energy_estimate S Q).tilt_hasDerivAt β V
lemma noise_cont_all : Continuous fun p : ℝ × Config G c × Config G c => S.noise p.1 p.2.1 p.2.2 := by
  unfold StepData.noise StepData.penaltyWeight
  fun_prop (disch := intro _; exact (S.penaltyZ_pos _).ne')
@[simp] lemma noise_zero (Q V : Config G c) : S.noise 0 Q V = 1 := by simp only [noise_tilt,tilt_zero]

def tagWeight (β : ℝ) (t : S.Choices) (U : Config G f) (V : Config G c) :=
  S.likelihood U t * S.noise β (S.prediction U t) V
def tagEnergy (t : S.Choices) (U : Config G f) (V : Config G c) :=
  noiseEnergy S (S.prediction U t) V
def tagSlope (β : ℝ) (t : S.Choices) (U : Config G f) (V : Config G c) :=
  tagWeight S β t U V * (noiseMean S G β - tagEnergy S t U V)

lemma joint_prediction_meas (h : S.patch.Branches S.kernel G) (t : S.Choices) :
    Measurable fun p : Config G f × Config G c => (S.prediction p.1 t,p.2) :=
  ((S.prediction_meas h t).comp measurable_fst).prodMk measurable_snd

lemma tagEnergy_meas (h : S.patch.Branches S.kernel G) (t : S.Choices) :
    Measurable fun p : Config G f × Config G c => tagEnergy S t p.1 p.2 := by
  change Measurable ((fun y : Config G c × Config G c => noiseEnergy S y.1 y.2) ∘
    fun p : Config G f × Config G c => (S.prediction p.1 t,p.2))
  exact (noiseEnergy_cont (G:=G) S).measurable.comp (joint_prediction_meas S h t)

lemma tagWeight_nonneg (t : S.Choices) (β : ℝ) (U : Config G f) (V : Config G c) :
    0 ≤ tagWeight S β t U V := mul_nonneg (S.likelihood_pos U t) (noise_pos ..).le
lemma tag_hasDerivAt (β : ℝ) (t : S.Choices) (U : Config G f) (V : Config G c) :
    HasDerivAt (fun b => tagWeight S b t U V) (tagSlope S β t U V) β := by
  simpa only [tagWeight,tagSlope,tagEnergy,mul_assoc] using
    (noise_hasDerivAt S (S.prediction U t) V β).const_mul (S.likelihood U t)
lemma tagSlope_bound (β : ℝ) (t : S.Choices) (U : Config G f) (V : Config G c) :
    ‖tagSlope S β t U V‖ ≤ noiseCap S * tagWeight S β t U V := by
  rw [tagSlope, norm_mul, Real.norm_of_nonneg (tagWeight_nonneg ..), mul_comm (noiseCap S)]
  refine mul_le_mul_of_nonneg_left (abs_le.mpr ?_) (tagWeight_nonneg ..)
  obtain ⟨h1,h2⟩ := noiseMean_bound (G:=G) S β
  unfold tagEnergy; have h := energy_estimate S (S.prediction U t)
  constructor <;> linarith [h.nonneg V,h.bound V]
lemma tag_estimate (h : S.patch.Branches S.kernel G) (t : S.Choices) :
    WeightEstimate (fun β (p : Config G f × Config G c) => tagWeight S β t p.1 p.2)
      (fun β p => tagSlope S β t p.1 p.2) (noiseCap S) (noiseCost S) := by
  have hn (β : ℝ) : Measurable fun p : Config G f × Config G c => S.noise β (S.prediction p.1 t) p.2 := by
    change Measurable ((fun y : Config G c × Config G c => S.noise β y.1 y.2) ∘
      fun p : Config G f × Config G c => (S.prediction p.1 t,p.2))
    exact (S.noise_cont β).measurable.comp (joint_prediction_meas S h t)
  have hl : Measurable fun p : Config G f × Config G c => S.likelihood p.1 t :=
    (S.likelihood_meas h t).comp measurable_fst
  have hm (β : ℝ) : Measurable fun p : Config G f × Config G c => tagWeight S β t p.1 p.2 :=
    hl.mul (hn β)
  refine ⟨hm,fun β => (hm β).mul (measurable_const.sub (tagEnergy_meas S h t)),fun β p => tagWeight_nonneg ..,
    fun hb p => ?_,fun β p => tagSlope_bound ..,fun β p => tag_hasDerivAt ..,noiseCap_nonneg _,
    fun R _ => (noiseCost_pos S R).le⟩
  have ht : S.likelihood p.1 t ≤ 1 := by
    rw [← S.chosen h p.1]; exact Finset.single_le_sum (fun k _ => S.likelihood_pos _ k) (Finset.mem_univ _)
  exact (mul_le_of_le_one_left (noise_pos ..).le ht).trans (noise_bounds S hb _ _).2
end YM.Push.BetaTransport
