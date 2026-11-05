import YM.Pert.Parity.Cloud
/-! Bare rescaling; this involves simultaneous negation of Gaussian coordinates, not an independent claim that the gauge potential or the lattice action is even. For an insertion jet, removing one coupling power adds a sign. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.Pert.Parity
open MeasureTheory Lattice Orb Labels Function
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}
local notation "coef" => PowerSeries.coeff (R:=ℂ)
/-- Formal `g↦-g`. -/
abbrev bounce := PowerSeries.rescale (-1:ℂ)

lemma scaleJet_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Potential G n → E) (m : ℕ) (x : Coords G n) : scaleJet f m (-x) = (-1:ℝ)^m • scaleJet f m x := by
  unfold scaleJet; rw [map_neg]; rw [show (fun _ : Fin m => -(expand G n x)) = (fun i:Fin m => (-1:ℝ) • ((fun _ : Fin m => expand G n x) i)) by funext; exact (neg_one_smul ℝ _).symm, (iteratedFDeriv ℝ m f 0).map_smul_univ (fun _:Fin m=>-1) (fun _=>_)]; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_comm]
lemma unmarked_neg (x : Coords G n) : unmarked G n (-x) = bounce (unmarked G n x) := by ext m; rw [PowerSeries.coeff_rescale]; simp only [unmarked,PowerSeries.coeff_mk,scaleJet_neg,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
lemma actionR_neg (x : Coords G n) : actionR G n (-x) = bounce (actionR G n x) := by
  ext m
  rw [PowerSeries.coeff_rescale]; by_cases h : m=0
  · simp [h,actionR]
  simp [h,actionR,scaleJet_neg,smul_eq_mul,pow_add]
lemma expR_neg {D : Type*} [NormedAddCommGroup D] (p : JetArray D) (h : ∀ v, p (-v)=bounce (p v)) : ∀ v, expR p (-v)=bounce (expR p v) := by
  intro v
  ext m
  simp only [PowerSeries.coeff_rescale,expR,PowerSeries.coeff_mk,h,← map_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; exact mul_left_comm ..
lemma weight_neg (x : Coords G n) : weight G n (-x)=bounce (weight G n x) := by simp only [weight,Pi.mul_apply,expR_neg _ actionR_neg, unmarked_neg, map_mul]
lemma ps_const (c : ℂ) : bounce (PowerSeries.C c) = PowerSeries.C c := by ext m; rw [PowerSeries.coeff_rescale]; by_cases h : m=0 <;> simp [PowerSeries.coeff_C,h]
lemma bare_neg (h : ℝ) (o : Site n) (v : Coords G n) (z : Key G) : Bare.seriesLex h o (-v) z = bounce (- Bare.seriesLex h o v z) := by
  ext m; rw [PowerSeries.coeff_rescale]; simp [Bare.seriesLex, scaleJet_neg, Complex.real_smul, pow_succ]

lemma expect_reflect {p q : JetArray (Coords G n)} (hp : Ready p) (h : ∀ v, p (-v)=bounce (q v)) : expect p = bounce (expect q) := by
  ext j
  rw [PowerSeries.coeff_rescale,expect,PowerSeries.coeff_mk]
  have he := integral_cloud (covarianceM G n) (fun x=> coef j (p x)) (hp j).1.aestronglyMeasurable
  change (∫ x, coef j (p (-x)) ∂(data G n)) = ∫ x, coef j (p x) ∂(data G n) at he
  rw [←he]; simp only [h,PowerSeries.coeff_rescale,integral_const_mul,expect,PowerSeries.coeff_mk]
lemma vacuum_reflect : bounce (vacuum G n)=vacuum G n := (expect_reflect weight_ready weight_neg).symm
lemma inv_vac : bounce (vacuum G n)⁻¹=(vacuum G n)⁻¹ := by
  let u := (vacuum G n)⁻¹
  have he : vacuum G n * u = 1 := by simpa [u,vacuum, Orb.normalize] using normalized_unit (G:=G) (n:=n)
  have hh : vacuum G n * bounce u = 1 := by rw [←vacuum_reflect,←map_mul,he,map_one]
  calc
    bounce (vacuum G n)⁻¹ = u * (vacuum G n * bounce u) := by rw [← mul_assoc,mul_comm u,he,one_mul]
    _ = u := by rw [hh,mul_one]
lemma normalize_reflect {p q : JetArray (Coords G n)} (hp : Ready p) (h : ∀ v, p (-v)=bounce (q v)) : normalize p = bounce (normalize q) := by
  unfold Orb.normalize
  rw [expect_reflect (q:=weight G n * q) (Ready.mul weight_ready hp),map_mul,inv_vac]
  exact fun v=> by simp only [Pi.mul_apply,weight_neg,h v,map_mul]
end YM.Pert.Parity
