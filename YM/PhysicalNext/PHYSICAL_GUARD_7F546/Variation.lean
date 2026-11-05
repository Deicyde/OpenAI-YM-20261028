import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TotalCost
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Tails


/-!
# Weighted likelihood price on the same pair of marginals

In common centered fluctuation coordinates, target `shift C δ`, reference
`cloud B`; old `cloud C` coordinate at reference z would thus be z - δ.
Consequently the likelihood of target against reference is `replace C B
(-δ)`, **including** its determinants. Bound the weighted *variation* from
the Workshop log price and actual absolute moments on **both** sides. Do
not bound growing powers of the likelihood from its log estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546
open MeasureTheory Function Filter Finset
open YM.Next.SectorChange.Gaussian YM.SectorTools.PhysicalGaussianSwitch
open YM.AnalyticBridge.LocalGaussianLaws
open scoped Topology BigOperators ENNReal
local notation "Covar" => YM.Next.SectorChange.Gaussian.Table

/-- Chosen high-moment order. -/
def highMoment (D : ℕ) := 2 * D + 2

/-- Target fluctuation price once the standardized shift costs at most one. -/
def momentFare (K D : ℕ) (U : ℝ) := momentPrice K (highMoment D) U 1


def powerDecay (x : ℝ) := x ^ (-(7/64):ℝ)


/-- Weighted integral-error price. -/
def errorFare (K D : ℕ) (U x : ℝ) := (8 * (K:ℝ) * momentFare K D U) * powerDecay x


section pair
variable {I : Type} [Fintype I] [DecidableEq I]

lemma replace_likelihood (C B : Covar I) (δ : Vec I) :
    likelihood C δ B 0 = Density.replace C B (-δ) := by
  funext z
  rw [likelihood, zero_sub, sub_zero, Density.replace,
    AnalyticBridge.GaussianFieldAlignment.Relative.trade, Density.chip, Density.spice, sub_div,
    add_comm (-δ) z]

/-- Inputs at the named pair -- exported from the physical prices below. -/
structure PairPrice (C B : Covar I) (δ : Vec I) (x U : ℝ) : Prop where
  x_one : 1 ≤ x
  upper : 1 ≤ U
  C_pos : C.PosDef
  B_pos : B.PosDef
  C_entry i j : |C i j| ≤ U
  B_entry i j : |B i j| ≤ U
  shift_size i : |δ i| ≤ x ^ (-(1/8):ℝ)
  workshopLog (z : Vec I) :
    let P := x^(1/128:ℝ)
    |Real.log (Density.replace C B (-δ) z)| ≤
      x^(-(1/8):ℝ) * (P * Fintype.card I * (1 + 1^2) + (P^2 + P) * Density.energy z)

variable {C B : Covar I} {δ : Vec I} {x U : ℝ}

namespace PairPrice

variable (h : PairPrice C B δ x U)
include h



theorem exchange {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (f : Vec I → X) :
    (Integrable f (shift C δ) ↔
      Integrable (fun z => Density.replace C B (-δ) z • f z) (cloud B)) ∧
    (∫ z, f z ∂shift C δ) = ∫ z, Density.replace C B (-δ) z • f z ∂cloud B := by
  have he := shift_identity h.C_pos h.B_pos δ 0 f
  rwa [centered, replace_likelihood] at he

theorem moments {K : ℕ} (hK : Fintype.card I ≤ K) (q : ℕ) :
    let Y := momentPrice K q U 1
    MomentBound (shift C δ) q Y ∧ MomentBound (cloud B) q Y := by
  intro Y
  have hh : 0 ≤ U := zero_le_one.trans h.upper
  have hi i : |δ i| ≤ 1 := (h.shift_size i).trans
    (Real.rpow_le_one_of_one_le_of_nonpos h.x_one (by norm_num))
  refine ⟨shifted_moments C h.C_pos.posSemidef hK hh h.C_entry δ zero_le_one hi q,?_⟩
  rw [← centered B]
  exact shifted_moments B h.B_pos.posSemidef hK hh h.B_entry 0 zero_le_one (by simp) q

theorem log_price {K : ℕ} (hK : Fintype.card I ≤ K) (z : Vec I) :
    |Real.log (Density.replace C B (-δ) z)| ≤ 4 * (K:ℝ) * powerDecay x * weight 2 z := by
  have hx : 0 < x := zero_lt_one.trans_le h.x_one
  let P := x ^ (1/128:ℝ)
  have hp : 1 ≤ P := Real.one_le_rpow h.x_one (by norm_num)
  have hp' : P ≤ P^2 := by nlinarith only [hp]
  have hp0 : 0 ≤ P := zero_le_one.trans hp
  have hc : (Fintype.card I : ℝ) ≤ K := Nat.cast_le.mpr hK
  have hw : 1 ≤ weight 2 z := by unfold weight; nlinarith [norm_nonneg z]
  have hE : Density.energy z ≤ (K:ℝ) * weight 2 z := by
    unfold Density.energy dotProduct
    calc
      _ ≤ ∑ _i : I, weight 2 z := by
        apply sum_le_sum
        intro i hi
        rw [← sq, ← sq_abs]
        have ha := norm_le_pi_norm z i
        rw [Real.norm_eq_abs] at ha
        exact pow_le_pow_left₀ (abs_nonneg _) (le_trans ha (le_add_of_nonneg_left zero_le_one)) _
      _ = Fintype.card I * weight 2 z := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (weight_nonneg _ _)
  apply (h.workshopLog z).trans
  have hs : x^(-(1/8):ℝ) * P^2 = powerDecay x := by
    unfold P powerDecay
    rw [sq, ← Real.rpow_add hx, ← Real.rpow_add hx]; norm_num
  have hk : 0 ≤ (K:ℝ) := by positivity
  change x^(-(1/8):ℝ) * (P * Fintype.card I * _ + _) ≤ _
  have h1 : P * Fintype.card I * (1 + 1^2) ≤ 2 * P^2 * K * weight 2 z := by
    calc
      _ ≤ P^2 * (K:ℝ) * (1+1^2) := by gcongr
      _ = 2 * P^2 * (K:ℝ) := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hw
  have h2 : (P^2 + P) * Density.energy z ≤ 2 * P^2 * K * weight 2 z := by
    calc
      _ ≤ (P^2 + P) * ((K:ℝ) * weight 2 z) := mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ (2*P^2) * ((K:ℝ) * weight 2 z) := mul_le_mul_of_nonneg_right (by linarith)
        (mul_nonneg hk (weight_nonneg _ _))
      _ = _ := by ring
  apply (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : 0 ≤ x^(-(1/8):ℝ))).trans_eq
  rw [← hs]; ring

/-- Weight the absolute density difference; no linearization of the likelihood. -/
theorem variation {K : ℕ} (hK : Fintype.card I ≤ K) (D : ℕ) :
    let L := Density.replace C B (-δ)
    Integrable (fun z => |L z - 1| * weight D z) (cloud B) ∧
      (∫ z, |L z - 1| * weight D z ∂cloud B) ≤ errorFare K D U x := by
  intro L
  have hl z : 0 < L z := Density.replace_pos _ _ h.C_pos h.B_pos _ _
  let d := 4 * (K:ℝ) * powerDecay x
  let q := highMoment D
  let R (z : Vec I) := weight q z
  let μ := shift C δ
  let ν := cloud B
  have hx : 0 < x := zero_lt_one.trans_le h.x_one
  have hd : 0 ≤ d := by unfold d powerDecay; positivity
  obtain ⟨hm,hb⟩ := h.moments hK q
  have he := h.exchange R
  have hi : Integrable (fun z => L z * R z) ν := he.1.mp hm.auth
  let H z := d * (L z * R z + R z)
  have hI : Integrable H ν := (hi.add hb.auth).const_mul d
  let g (z : Vec I) := |L z - 1| * weight D z
  have hg : Measurable g := by
    apply Measurable.mul _ (weight_continuous _).measurable
    exact ((Density.replace_on C B _).sub measurable_const).abs
  have hPoint z : g z ≤ H z := by
    have hs : |Real.log (L z)| ≤ d * weight 2 z := h.log_price hK z
    have h1 : |L z - 1| ≤ d * weight 2 z * L z + d * weight 2 z :=
      (Density.delta (hl z)).trans (add_le_add (mul_le_mul_of_nonneg_right hs (hl z).le) hs)
    have h2 : weight 2 z * weight D z ≤ R z := by
      rw [← weight_add]
      exact weight_mono z (show 2 + D ≤ highMoment D by unfold highMoment; omega)
    unfold g
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (weight_nonneg D z)
      _ = d * (L z + 1) * (weight 2 z * weight D z) := by ring
      _ ≤ d * (L z + 1) * R z := mul_le_mul_of_nonneg_left h2
        (mul_nonneg hd (by linarith only [hl z]))
      _ = _ := by unfold H; ring
  have hInt : Integrable g ν := hI.mono' hg.aestronglyMeasurable (Eventually.of_forall
    (fun z => (Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (weight_nonneg D z))).trans_le (hPoint z)))
  refine ⟨hInt,(integral_mono hInt hI hPoint).trans ?_⟩
  change (∫ z, H z ∂ν) ≤ errorFare K D U x
  have hV : (∫ z, L z * R z ∂ν) = ∫ z, R z ∂μ := he.2.symm
  unfold H
  rw [integral_const_mul, integral_add hi hb.auth, hV]
  apply (mul_le_mul_of_nonneg_left (add_le_add hm.bound hb.bound) hd).trans_eq
  unfold d q errorFare momentFare
  ring

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Uniform in all tests with a polynomial-class price. Carries true tails
separately; use `exchange` for exact scalar/likelihood version. -/
theorem comparing {K : ℕ} [CompleteSpace X] (hK : Fintype.card I ≤ K)
    {f : Vec I → X} {D : ℕ} {c : ℝ} (ht : TestPrice f D c) :
    let q := highMoment D
    let A := momentFare K D U
    let μ := shift C δ
    let ν := cloud B
    TailPrice μ f q D A c ∧ TailPrice ν f q D A c ∧
      ‖(∫ z, f z ∂μ) - ∫ z, f z ∂ν‖ ≤ c * errorFare K D U x := by
  intro q A μ ν
  obtain ⟨hm,hb⟩ := h.moments hK q
  have hq : 2 * D ≤ q := by unfold q highMoment; omega
  have hm' := hm.price ht hq
  have hb' := hb.price ht hq
  obtain ⟨hi,hV⟩ := h.variation hK D
  refine ⟨hm', hb', ?_⟩
  let L := Density.replace C B (-δ)
  obtain ⟨hv,he⟩ := h.exchange f
  have hInt : Integrable (fun z => L z • f z) ν := hv.mp hm'.auth
  change ‖(∫ z, f z ∂shift C δ) - _‖ ≤ _
  rw [he, ← integral_sub hInt hb'.auth]
  apply (norm_integral_le_integral_norm _).trans
  let g (z : Vec I) := |L z - 1| * weight D z
  have hg : Integrable g ν := hi
  have hr z : ‖L z • f z - f z‖ ≤ c * g z := by
    rw [show L z • f z - f z = (L z - 1) • f z by rw [sub_smul, one_smul],
      norm_smul, Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left (ht.size z) (abs_nonneg _)).trans_eq
    unfold g; ring
  calc
    _ ≤ ∫ z, c * g z ∂ν := integral_mono (hInt.sub hb'.auth).norm (hg.const_mul _) hr
    _ ≤ _ := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hV ht.nonneg



end PairPrice
end pair
end YM.PhysicalNext.PhysicalGuard7f546
