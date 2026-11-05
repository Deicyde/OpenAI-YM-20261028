import YM.Next.SCHEDULE.Stadium
import YM.SectorNext.VACUUM_NORMALIZATION.Panel
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Schur


/-!
# Uniform support costs under elliptic checks

Exact `price` uses entries of a supported marginal. Get uniform
quantitative estimates if those matrices inherit ellipticity (without a
uniform spectral check even support of size one need not have a bounded, or
even finite, price). Coarse estimates suffice here, retaining exponential
per-support and affine size costs. -/

set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch
open Function Set Matrix MeasureTheory
open Real (sqrt)
open Next.SectorChange.Gaussian
open FreeResolvent (insertion)
open Precision (Numeric)
open SectorNext.Vacuum.Panel (determinant)
open scoped Topology BigOperators ENNReal
local notation "Covar" => Next.SectorChange.Gaussian.Table

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {A D : Covar I} {η L K p : ℝ}

omit [DecidableEq I] in
lemma priced_pos (h : A.IsSymm) (he : Numeric A η L) (hh : 0 < η) : A.PosDef :=
  posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_iff_isSymm.mpr h, fun _ hx => star_vec _ ▸
    lt_of_lt_of_le (mul_pos hh (sumsq_pos hx)) (he _).1⟩

lemma inverse_dual (hA : A.PosDef) (v z : Vec I) : 2*(z ⬝ᵥ v) - quad A v ≤ quad A⁻¹ z := by
  have h := quad_nonneg hA (v-A⁻¹ *ᵥ z)
  rw [quad_sub (symm_pos hA),mulVec_mulVec,A.mul_nonsing_inv (unit_det hA),one_mulVec,dotProduct_comm v] at h
  have ht : quad A (A⁻¹ *ᵥ z)=quad A⁻¹ z := by
    unfold quad; rw [mulVec_mulVec,A.mul_nonsing_inv (unit_det hA),one_mulVec,dotProduct_comm]
  linarith only [h,ht]

lemma inverse_exact (hA : A.PosDef) (z : Vec I) :
    quad A⁻¹ z=2*(z ⬝ᵥ (A⁻¹ *ᵥ z))-quad A (A⁻¹ *ᵥ z) := by
  unfold quad; rw [mulVec_mulVec,A.mul_nonsing_inv (unit_det hA),one_mulVec,dotProduct_comm (A⁻¹ *ᵥ z) z]; ring

omit [DecidableEq I] in
private lemma dot_complete {η : ℝ} (hh : 0 < η) (t x : Vec I) :
    2*(x ⬝ᵥ t)-η*(t ⬝ᵥ t) ≤ η⁻¹*(x ⬝ᵥ x) := by
  have ht := sumsq_nonneg (η • t-x)
  rw [sub_dotProduct,dotProduct_sub,dotProduct_sub,smul_dotProduct,dotProduct_smul,dotProduct_smul,
    smul_dotProduct,dotProduct_comm t x] at ht
  simp only [smul_eq_mul] at ht
  apply le_of_mul_le_mul_left (a:=η) ?_ hh
  rw [← mul_assoc,mul_inv_cancel₀ hh.ne',one_mul]; linarith only [ht]

lemma inverse_upper (hA : A.PosDef) (hh : 0 < η) (h : ∀ x : Vec I,η*(x ⬝ᵥ x)≤quad A x) (x : Vec I) :
    quad A⁻¹ x ≤ η⁻¹*(x ⬝ᵥ x) := calc
  _ = _ := inverse_exact hA x
  _ ≤ 2*(x ⬝ᵥ (A⁻¹ *ᵥ x))-η*((A⁻¹ *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ x)) := sub_le_sub_left (h _) _
  _ ≤ _ := dot_complete hh _ x
lemma inverse_lower (hA : A.PosDef) (hh : 0 < L) (h : ∀ x : Vec I,quad A x≤L*(x ⬝ᵥ x)) (x : Vec I) :
    L⁻¹*(x ⬝ᵥ x) ≤ quad A⁻¹ x := by
  let v := L⁻¹ • x
  calc
    _ = 2*(x ⬝ᵥ v)-L*(v ⬝ᵥ v) := by
      unfold v; rw [smul_dotProduct,dotProduct_smul]; simp only [smul_eq_mul]
      field_simp; ring
    _ ≤ 2*(x ⬝ᵥ v)-quad A v := sub_le_sub_left (h v) _
    _ ≤ _ := inverse_dual hA _ _

structure Elliptic (K : ℝ) (A : Covar I) : Prop where
  tall : 1 ≤ K
  symm : A.IsSymm
  numeric : Numeric A K⁻¹ K

namespace Elliptic
variable (h : Elliptic K A)
include h
omit [DecidableEq I] in
lemma positive : 0 < K := zero_lt_one.trans_le h.tall
omit [DecidableEq I] in
lemma posDef : A.PosDef := priced_pos h.symm h.numeric (inv_pos.mpr h.positive)
omit [DecidableEq I] in
lemma upper (x : Vec I) : quad A x ≤ K*(x ⬝ᵥ x) := (h.numeric x).2
omit [DecidableEq I] in
lemma lower (x : Vec I) : K⁻¹*(x ⬝ᵥ x) ≤ quad A x := (h.numeric x).1
lemma inverse : Elliptic K A⁻¹ := by
  refine ⟨h.tall,symm_pos h.posDef.inv,fun x => ⟨inverse_lower h.posDef h.positive h.upper x,?_⟩⟩
  simpa only [inv_inv] using! inverse_upper h.posDef (inv_pos.mpr h.positive) h.lower x
omit [DecidableEq J] in
lemma sub (e : J ↪ I) : Elliptic K (A.submatrix e e) := by
  refine ⟨h.tall,h.symm.submatrix _,fun x => ?_⟩
  have ht := h.numeric (insertion e *ᵥ x)
  simpa only [insertion.dot_insert _ e.injective, insertion.dot_compress] using ht
lemma schur (e : J ↪ I) : Elliptic K (schurCov e A) := (h.inverse.sub e).inverse
omit [DecidableEq I] in
lemma enlarge (he : K ≤ L) : Elliptic L A := by
  refine ⟨h.tall.trans he,h.symm,fun x => ⟨le_trans ?_ (h.lower x),(h.upper x).trans ?_⟩⟩
  all_goals gcongr
  all_goals first | exact sumsq_nonneg _ | exact h.positive

lemma op (x : Vec I) : let v:=A⁻¹ *ᵥ x; v ⬝ᵥ v ≤ K^2*(x ⬝ᵥ x) := by
  intro v
  have ht : quad A v=quad A⁻¹ x := by unfold quad v; rw [mulVec_mulVec,A.mul_nonsing_inv (unit_det h.posDef), one_mulVec,dotProduct_comm (A⁻¹ *ᵥ x)]
  have he := (h.lower v).trans (ht.le.trans (h.inverse.upper x))
  have hz := mul_le_mul_of_nonneg_left he h.positive.le
  rwa [← mul_assoc, mul_inv_cancel₀ h.positive.ne',one_mul,← mul_assoc,← sq] at hz

lemma det_upper : A.det ≤ K^Fintype.card I :=
  (determinant h.posDef.isHermitian h.numeric (inv_pos.mpr h.positive)).2.1.2
lemma sqrt_upper : sqrt A.det ≤ K^Fintype.card I := by
  let Y := K ^ Fintype.card I
  have h1 : 1 ≤ Y := one_le_pow₀ h.tall
  exact (Real.sqrt_le_left (zero_le_one.trans h1)).mpr (h.det_upper.trans (by nlinarith))
lemma sqrt_inv_upper : (sqrt A.det)⁻¹ ≤ K^Fintype.card I := by
  simpa only [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Real.sqrt_inv] using h.inverse.sqrt_upper
end Elliptic

theorem mixed_band (hA : Elliptic K A) (hD : Elliptic K D)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (he : (p-1)*K ≤ (2*K)⁻¹) : Elliptic (2*K) (mixed A D p) := by
  have hk:=hA.positive
  refine ⟨(by linarith [hA.tall]), mixed_symm hA.posDef hD.posDef,fun x => ?_⟩
  let s := x ⬝ᵥ x; have hs : 0≤s:=sumsq_nonneg _
  have h1 := hA.inverse.numeric x; have h2 := hD.inverse.numeric x
  change (K⁻¹*s≤quad _ _ ∧ quad _ _ ≤ K*s) at h1 h2
  change ((2*K)⁻¹*s≤quad _ _ ∧ quad _ _ ≤ (2*K)*s)
  unfold mixed; simp_rw [quad_sum,quad_smul]; constructor
  · have h3 := mul_le_mul h1.1 hp (by norm_num : (0:ℝ) ≤ 1) (quad_nonneg hA.posDef.inv x)
    have h4 := mul_le_mul_of_nonneg_left h2.2 (sub_nonneg.mpr hp)
    have ht : K⁻¹ = 2*(2*K)⁻¹ := by field_simp
    linarith only [h3,h4, mul_le_mul_of_nonneg_right he hs, show K⁻¹*s=(2*(2*K)⁻¹)*s by rw [← ht]]
  have h3 := mul_le_mul hp2 h1.2 (quad_nonneg hA.posDef.inv x) (by norm_num : (0:ℝ)≤2)
  have h4 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) (quad_nonneg hD.posDef.inv x)
  linarith

/-- One admissible p uniform over periods if K uniform (note cost to the
other exponent as K grows). -/
def power (K : ℝ) := 1+(2*K*K)⁻¹


-- purposely loose determinant bill. Retains per-coordinate factor. n=0 OK
def tariff (K : ℝ) (n : ℕ) (b : ℝ) := (2*K^6)^n * Real.exp (4*K^3 * b)

/-- Counts all coordinates on the stated system; spend only on the
*support* systems after `price_on`! -/
theorem total (hA : Elliptic K A) (hD : Elliptic K D) (v : Vec I)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (he : (p-1)*K ≤ (2*K)⁻¹) :
    price A D p v ≤ tariff K (Fintype.card I) (v ⬝ᵥ v) := by
  let n := Fintype.card I
  let q := sqrt D.det / sqrt A.det
  have hQ : 0 < q := div_pos (Real.sqrt_pos.mpr hD.posDef.det_pos) (Real.sqrt_pos.mpr hA.posDef.det_pos)
  let M := mixed A D p
  have hm : Elliptic (2*K) M := mixed_band hA hD hp hp2 he
  have hK := hA.positive; have hk := hA.tall
  have h1 : 1 ≤ K^n := one_le_pow₀ hk
  have hq : q ≤ K^n*K^n := by
    unfold q; rw [div_eq_mul_inv]; exact mul_le_mul hD.sqrt_upper hA.sqrt_inv_upper (by positivity) (by positivity)
  have ht : q^p ≤ (K^n*K^n)^2 := calc
    _ ≤ (K^n*K^n)^p := Real.rpow_le_rpow hQ.le hq (zero_le_one.trans hp)
    _ ≤ (K^n*K^n)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by nlinarith) hp2
    _ = _ := Real.rpow_two _
  have hh : sqrt (M⁻¹).det/sqrt D.det ≤ (2*K)^n*K^n := by
    rw [div_eq_mul_inv]; exact mul_le_mul hm.inverse.sqrt_upper hD.sqrt_inv_upper (by positivity) (by positivity)
  let s := v ⬝ᵥ v; have hs : 0 ≤ s := sumsq_nonneg _
  have hu : quad (mixed A D p)⁻¹ (debt A p v) ≤ 8*K^3*s := by
    let t:=A⁻¹ *ᵥ v
    calc
      _ ≤ (2*K)*((debt A p v) ⬝ᵥ (debt A p v)) := hm.inverse.upper _
      _ = (2*K)*(p^2*(t ⬝ᵥ t)) := by unfold t debt; rw [smul_dotProduct,dotProduct_smul]; simp only [smul_eq_mul]; ring
      _ ≤ (2*K)*(4*(K^2*s)) := by
        gcongr
        · exact sumsq_nonneg _
        · nlinarith
        · exact hA.op v
      _ = _ := by ring
  have hl := quad_nonneg hA.posDef.inv v
  have hw : (K^n*K^n)^2*((2*K)^n*K^n)=(2*K^6)^n := by simp_rw [mul_pow,← pow_mul]; ring
  unfold price tariff
  rw [← hw]
  exact mul_le_mul (mul_le_mul ht hh (by positivity) (by positivity)) (Real.exp_monotone (by change _ ≤ 4*K^3*s; nlinarith)) (Real.exp_pos _).le (by positivity)

namespace Sufficient
variable {R : Vec I → Vec J} {S T : Covar J} {a d : Vec I}


end Sufficient
end YM.SectorTools.PhysicalGaussianSwitch
