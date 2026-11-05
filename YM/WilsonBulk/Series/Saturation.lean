import YM.WilsonBulk.Series.Ideal

/-! unit system for factor assembly. No unit estimate in β. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open scoped Topology Classical ENNReal BigOperators
open Function Filter PowerSeries
variable {A : Type} [CommRing A] [Algebra ℝ A] {p q r : PowerSeries A}
lemma column_ode_id (D : PowerSeries A) (hp : constantCoeff p=constantCoeff q) (he : clockD A p=D*p) (hf : clockD A q=D*q) : p=q := by
  ext1 i
  induction i using Nat.strong_induction_on with
  | h i ih=>
     cases i with
     | zero => simpa only [coeff_zero_eq_constantCoeff] using hp
     | succ i=>
        have H : Steps (i+1) p q := ih
        refine smul_right_injective _ (show ((i+1:ℕ):ℝ)≠0 by positivity) ?_
        dsimp only; rw [← clock_coeff, ← clock_coeff, he,hf]
        exact (Steps.mul Steps.self H) i (by omega)
lemma tide_both (hp : constantCoeff p=0) (hq : constantCoeff q=0) : tide (p+q)=tide p*tide q := by
  apply column_ode_id (D:=clockD A (p+q))
  · simp [tide_const]
  · rw [differentiate_time (p:=p+q) (by simp [hp,hq]), mul_comm]
  rw [D_leib, differentiate_time hp, differentiate_time hq, map_add]; ring
@[simp] lemma tide_zero : tide (0:PowerSeries A)=1 := by
  have h0 : constantCoeff (0:PowerSeries A)=0 := map_zero _
  apply column_ode_id (D:=0)
  · simp [tide_const]
  · rw [differentiate_time h0]; simp
  simp
lemma tide_neg (hp : constantCoeff p=0) : tide (-p)*tide p=1 := by rw [← tide_both (p:=-p) (by simp [hp]) hp]; simp
-- division formula input and output; for p with unit constant
omit [Algebra ℝ A] in
lemma unit_const_one (hp : constantCoeff p=1) : IsUnit p := isUnit_iff_constantCoeff.mpr (by rw [hp]; exact isUnit_one)
def recover (p : PowerSeries A) : PowerSeries A := if h:IsUnit p then ↑h.unit⁻¹ else 0
omit [Algebra ℝ A] in
lemma recover_mul (hp : IsUnit p) : recover p*p=1 := by unfold recover; simp_rw [dif_pos hp]; exact (congr_arg (fun z:PowerSeries A=> (↑hp.unit⁻¹ : PowerSeries A) * z) hp.unit_spec).symm.trans (Units.inv_mul hp.unit)
lemma recover_tide (hp : constantCoeff p=0) : recover (tide p)=tide (-p) := by
  apply (tide_unit p).mul_left_inj.mp; rw [recover_mul (tide_unit p),tide_neg hp]
def quotient (p q : PowerSeries A) : PowerSeries A := p*recover q
omit [Algebra ℝ A] in
lemma quotient_pay (hq : IsUnit q) : quotient p q * q=p := by unfold quotient; rw [mul_assoc,recover_mul hq,mul_one]
lemma quotient_terms (hp : constantCoeff p=0) (hq : constantCoeff q=0) : quotient (tide p) (tide q)=tide (p-q) := by
  unfold quotient; rw [recover_tide hq,sub_eq_add_neg,tide_both hp (by simp [hq])]
end YM.WilsonBulk
