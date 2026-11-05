import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Review

/-!
# Gauge-coercivity, pre-L

Kill *all* of that shift by local gauge normal form, including constants.
Produce actual quantitative lower bound before any torus sizes.

Use alternative div-gauge with penalty from
    F(v) = d₀ᴴ a + L² paletteᴴ χ
on increments v. Complementary to the fine gauge: gauge increments (up to
sign) lead to positive site operator Δ + L² paletteᴴ palette.
Input ∇ and L times palette control site norm divided by L (`house`);
`‖F‖` alone controls `rent` of pure-gauge increments (`living`,
also using L² paletteᴴ has cost at most one). Combine with `twist_free`.
`Real` applies to real fields, then twist estimates for pricing derivatives of
the classical branch. No relation asserted between determinants in this gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG Work.F06
open Pre.Centered YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate InnerProductSpace
variable {c f : Side} (S : StepData c f)
local notation "L" => (S.patch.L.val:ℝ)
local notation "j" => S.patch.J
local notation "D" => drawC f 1
local notation "d₀" => drawC f 0
local notation "d'" => drawC c 0
local notation "Y" => Form f 1
local notation "A" => Form f 0
local notation "V" => Form c 0
local notation "B₀" => approached (palette S)
local notation "M" => approached (Precision.mean S)

def upkeep (y : Y) (v : V) := d₀ᴴ *ᵥ y + (↑(L^2):ℂ) • (B₀ᴴ *ᵥ v)
lemma upbeat (v : V) : ell2 ((↑(L^2):ℂ) • (B₀ᴴ *ᵥ v)) ≤ ell2 v := by
  apply le_trans _ ((mul_le_mul_of_nonneg_left (palateT S v) (sq_nonneg L)).trans_eq ?_)
  · rw [ell_smul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact mul_inv_cancel_left₀ (pow_ne_zero 2 (side_pos S.patch.L).ne') _
lemma uptime (y : Y) (v : V) : ell2 (upkeep S y v) ≤ rent S y v := by
  refine (ell_tri ..).trans ((add_le_add le_rfl (upbeat S v)).trans ?_); unfold rent
  linarith [ell_nonneg (D *ᵥ y),div_nonneg (ell_nonneg y) (side_pos S.patch.L).le]

def resident (i : ℕ) := lateFee⁻¹+(pass i)⁻¹*(1+lateFee⁻¹)
lemma resident_pos (i : ℕ) : 0 < resident i := by unfold resident; have h := late_pos; have g := pass_pos i; positivity
lemma house (u : A) : ell2 u/L ≤ resident j*(ell2 (d₀ *ᵥ u) + L*ell2 (B₀ *ᵥ u)) := by
  obtain ⟨a,b,h,g,rfl⟩ := split_from S u
  let T := ell2 (d₀ *ᵥ (a+b)); let P := ell2 (B₀ *ᵥ (a+b))
  have hP : 0 ≤ P := ell_nonneg _; have hT : 0 ≤ T := ell_nonneg _; have hL := side_pos S.patch.L
  have he : ell2 a/L ≤ lateFee⁻¹*T := by
    rw [inv_mul_eq_div]; apply (le_div_iff₀ late_pos).mpr
    rw [show ell2 a/L*lateFee=lateFee/L*ell2 a from by ring]; apply (light_top S h).trans
    unfold T; rw [Matrix.mulVec_add]; exact (growth S (top_up S h) (toe_up S g)).1
  have hv : ell2 b/L ≤ (pass j)⁻¹*(L*P+lateFee⁻¹*T) := by
    rw [inv_mul_eq_div]; apply (le_div_iff₀ (pass_pos j)).mpr
    have hc : ell2 (B₀ *ᵥ b) ≤ P+(L^2)⁻¹*ell2 a := by
      have H : B₀*ᵥ b=B₀ *ᵥ(a+b)- B₀ *ᵥ a := by rw [Matrix.mulVec_add]; abel
      rw [H]; exact (ell_sub ..).trans (add_le_add le_rfl (palate S a))
    apply ((show (ell2 b/L)*pass j ≤ L*ell2 (B₀ *ᵥ b) from by
      rw [div_mul_eq_mul_div]; apply (div_le_iff₀ hL).mpr
      linarith only [show pass j*ell2 b ≤ L^2*ell2 (B₀*ᵥ b) from fare S b g]).trans ((mul_le_mul_of_nonneg_left hc hL.le).trans ?_))
    rw [mul_add]; apply add_le_add le_rfl; convert! he using 1; field_simp
  have hb := add_le_add he hv
  have hh := (div_le_div_of_nonneg_right (ell_tri a b) hL.le).trans_eq (add_div _ _ _)
  refine hh.trans (hb.trans ?_)
  unfold resident; change _ ≤ _*(T+L*P)
  have hm : 0 ≤ lateFee⁻¹ := inv_nonneg.mpr late_pos.le; have hw : 0 ≤ (pass j)⁻¹ := inv_nonneg.mpr (pass_pos j).le
  rw [add_mul]; apply add_le_add (mul_le_mul_of_nonneg_left (by linarith [mul_nonneg hL.le hP]) hm)
  rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith [mul_nonneg hm (mul_nonneg hL.le hP)]) hw

lemma mortgage (u : A) :
    dotProduct (star u) (upkeep S (d₀ *ᵥ u) (B₀ *ᵥ u))=(((ell2 (d₀ *ᵥ u))^2+(L*ell2 (B₀*ᵥ u))^2:ℝ):ℂ) := by
  rw [upkeep,dotProduct_add,dotProduct_smul,← adjoint_area,← adjoint_area, complex_count,complex_count,Complex.ofReal_add,mul_pow,Complex.ofReal_mul]; rfl
lemma consume (u : A) : ell2 (d₀ *ᵥ u)+L*ell2 (B₀*ᵥ u) ≤ (2*resident j)*L*ell2 (upkeep S (d₀*ᵥ u) (B₀*ᵥ u)) := by
  let x := ell2 (d₀ *ᵥ u); let y := L*ell2 (B₀ *ᵥ u); let z:=ell2 (upkeep S (d₀ *ᵥ u) (B₀ *ᵥ u))
  have hp := side_pos S.patch.L; have hx : 0 ≤ x := ell_nonneg _; have hy : 0 ≤ y := mul_nonneg hp.le (ell_nonneg _); have hz : 0 ≤ z := ell_nonneg _
  have hb : x^2+y^2 ≤ ell2 u*z := by
    have h := norm_area u (upkeep S (d₀*ᵥ u) (B₀*ᵥ u)); rw [mortgage, Complex.norm_real,Real.norm_of_nonneg (by positivity)] at h; exact h
  have hv := hb.trans (mul_le_mul_of_nonneg_right ((div_le_iff₀ hp).mp (house S u)) hz)
  change x^2+y^2 ≤ _*(x+y)*L*z at hv; change x+y ≤ _*z
  rcases eq_or_lt_of_le (add_nonneg hx hy) with he|he
  · rw [← he]; exact mul_nonneg (by have h : 0 ≤ resident j := (resident_pos _).le; positivity) hz
  exact le_of_mul_le_mul_left (a:=x+y) (by nlinarith only [sq_nonneg (x-y),hv]) he

def wellness (i : ℕ) := 1+4*resident i
lemma wellness_pos (i : ℕ) : 0<wellness i := by unfold wellness; have h := resident_pos i; positivity
lemma living (u : A) : rent S (d₀ *ᵥ u) (B₀ *ᵥ u) ≤ wellness j*ell2 (upkeep S (d₀*ᵥ u) (B₀*ᵥ u)) := by
  let z := ell2 (upkeep S (d₀*ᵥ u) (B₀*ᵥ u)); have hL := side_pos S.patch.L
  have hb : ell2 (d₀*ᵥ u)/L+ell2 (B₀ *ᵥ u) ≤ 2*resident j*z := by
    rw [show ell2 _/L + ell2 (B₀ *ᵥ u)=(ell2 (d₀ *ᵥ u)+L*ell2 (B₀ *ᵥ u))/L by field_simp]
    apply (div_le_iff₀ hL).mpr; apply (consume S u).trans_eq; unfold z; ring
  have he : ell2 (d₀ᴴ *ᵥ(d₀*ᵥ u)) ≤ z+ell2 (B₀ *ᵥ u) := by
    have hh := (ell_sub (upkeep S (d₀ *ᵥ u) (B₀ *ᵥ u)) ((↑(L^2):ℂ) • (B₀ᴴ *ᵥ (B₀ *ᵥ u)))).trans (add_le_add le_rfl (upbeat S _));
    conv_lhs at hh => rw [upkeep,add_sub_cancel_right];
    exact hh
  rw [rent,shadow,ell_zero]; unfold wellness; change _ ≤ _*z
  linarith [div_nonneg (ell_nonneg (d₀*ᵥ u)) hL.le]

def yard (i : ℕ) := farePlan i+wellness i*(1+farePlan i)
lemma yard_pos (i : ℕ) : 0<yard i := by unfold yard; have h := go_positive i; have ht := wellness_pos i; positivity
lemma energetic (y : Y) (v : V) : rent S y v ≤ yard j * (ell2 (D *ᵥ y)+ell2 (M*ᵥ y-d'*ᵥ v)+ell2 (upkeep S y v)) := by
  let e := ell2 (D *ᵥ y)+ell2 (M*ᵥ y-d'*ᵥ v); let x := ell2 (upkeep S y v)
  obtain ⟨u,hu⟩ := twist_free S y v
  let a := y+d₀*ᵥu; let b := v+B₀*ᵥu; change rent S a b ≤ farePlan j*e at hu
  have he := living S u
  have hh : upkeep S (d₀ *ᵥ u) (B₀ *ᵥ u) = upkeep S a b - upkeep S y v := by
    unfold a b upkeep; simp_rw [Matrix.mulVec_add, smul_add]; abel
  rw [hh] at he
  have hp : 0≤wellness j := (wellness_pos _).le; have hv : 0 ≤ farePlan j := (go_positive _).le
  have hx := he.trans (mul_le_mul_of_nonneg_left ((ell_sub ..).trans (add_le_add ((uptime S a b).trans hu) (le_refl x))) hp)
  have hy := (rent_sub S a (d₀*ᵥ u) b (B₀*ᵥ u)).trans (add_le_add hu hx)
  rw [show a-_=y from add_sub_cancel_right .., show b-_=v from add_sub_cancel_right ..] at hy
  apply hy.trans
  change _ ≤ yard j*(e+x)
  have hg : 0 ≤ e := add_nonneg (ell_nonneg _) (ell_nonneg _); have ht : 0 ≤ x := ell_nonneg _
  unfold yard; linarith [mul_nonneg hv ht, mul_nonneg hp hg,mul_nonneg hp (mul_nonneg hv ht)]
end YM.AnalyticNext.QuarticMatch.Hessian
