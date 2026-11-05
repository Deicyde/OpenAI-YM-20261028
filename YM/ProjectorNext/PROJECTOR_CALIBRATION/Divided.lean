import YM.ProjectorNext.PROJECTOR_CALIBRATION.Germ
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Telescope

/-!
# Finite coupons for polarized main and divergence

Analytic laws on parameters `(θ, β⁻¹ θ⁻²)`. After crossing one
leg, the weight costs θ^{l-1}; its derivative needs θ^{l-2}
instead; differentiating the channel itself costs NO amplitude inverse.
Handle l<2 using natural subtraction, including l=0 where mix is zero.
No analytic estimate in growing d. -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration.Coupon
open Function Filter Tensor Work Next.Foundations
open scoped Topology BigOperators ContDiff
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {l : ℕ} (B : Tensor.T X ℂ l) (Q : Module.End ℝ X) (d : ℕ)

abbrev Screen (X : Type*) := X → X × X
/-- energy part after one power of θ extracted from each snap filter. -/
def daylight (Z : Screen X) (θ : ℝ) (x : X) : ℂ := Cross.mix B Q (trim d Z θ x).1 (trim d Z θ x).2

lemma day_smooth (Z : Screen X) : ContDiff ℝ ω (uncurry (daylight B Q d Z)) := by
  refine contDiff_iff_contDiffAt.mpr fun p => Cross.mix_smooth B Q ?_ ?_
  · exact (trim_smooth d Z).fst.contDiffAt
  exact (trim_smooth d Z).snd.contDiffAt

omit [FiniteDimensional ℝ X] in
lemma day_value (Z : Screen X) (A : X) : daylight B Q d Z 0 A = Cross.mix B Q (fderiv ℝ Z 0 A).1 (fderiv ℝ Z 0 A).2 := by rw [daylight,trim_value]

abbrev Slides (X : Type*) := X → X × X × X × X

/-- Divergence terms; pack `(R,dR,channel,dchannel)` only first of which is
required to vanish. Keep χ as separate parameter from the stencil
coefficients. -/
def evening (Z : Slides X) (θ : ℝ) (χ : ℝ) (x : X) : ℂ :=
    let v := trim d Z θ x
    let w := Z 0+θ • v
    χ • ((θ^(2+(l-2)-l)) • Cross.rate B Q v.1 w.2.1 w.2.2.1 +
        (θ^(2+(l-1)-l)) • Cross.mix B Q v.1 w.2.2.2)

lemma eve_smooth (Z : Slides X) : ContDiff ℝ ω (fun p : ℝ × ℝ × X => evening B Q d Z p.1 p.2.1 p.2.2) := by
  unfold evening; dsimp only
  let v (p : ℝ × ℝ × X) := trim d Z p.1 p.2.2
  let w (p : ℝ × ℝ × X) := Z 0+p.1 • v p
  have hv : ContDiff ℝ ω v := (trim_smooth d Z).comp (contDiff_fst.prodMk contDiff_snd.snd)
  have hw : ContDiff ℝ ω w := contDiff_const.add (contDiff_fst.smul hv)
  apply ContDiff.smul (f:=fun p : ℝ × ℝ × X => p.2.1) (g:=fun p => _ + _) contDiff_snd.fst
  refine ContDiff.add ((contDiff_fst.pow _).smul (contDiff_iff_contDiffAt.mpr fun p =>
    Cross.rate_smooth B Q hv.fst.contDiffAt hw.snd.fst.contDiffAt hw.snd.snd.fst.contDiffAt)) ?_
  exact (contDiff_fst.pow _).smul (contDiff_iff_contDiffAt.mpr fun p => Cross.mix_smooth B Q hv.fst.contDiffAt hw.snd.snd.snd.contDiffAt)

omit [FiniteDimensional ℝ X] in
private lemma flat (h : l=0) (x y : X) : Cross.mix B Q x y=0 := by
  rw [Cross.mixSum]
  subst l; exact Finset.sum_of_isEmpty _ -- ?

def raw (p : X × X) := Cross.mix B Q p.1 p.2

def marked (p : X × X × X × X) := Cross.rate B Q p.1 p.2.1 p.2.2.1 + Cross.mix B Q p.1 p.2.2.2

lemma raw_smooth : ContDiff ℝ ω (raw B Q) :=
    contDiff_iff_contDiffAt.mpr fun _ => Cross.mix_smooth B Q contDiffAt_fst contDiffAt_snd

lemma marked_smooth : ContDiff ℝ ω (marked B Q) :=
    contDiff_iff_contDiffAt.mpr fun _ =>
      (Cross.rate_smooth B Q contDiffAt_fst contDiffAt_snd.fst contDiffAt_snd.snd.fst).add (Cross.mix_smooth B Q contDiffAt_fst contDiffAt_snd.snd.snd)

private lemma scaled (θ : ℝ) (ht : θ ≠ 0) (χ : ℝ) (x : ℂ) (l k : ℕ) (hk : l≤2+k) :
    θ⁻¹^l • ((χ*θ^2) • (θ^k • x)) = χ • (θ^(2+k-l) • x) := by
  have he : θ^l*θ^(2+k-l)= θ^2 * θ^k := by rw [← pow_add,Nat.add_sub_of_le hk, pow_add]
  simp_rw [smul_smul,inv_pow]
  congr 1
  field_simp;  nth_rw 1 [mul_assoc]; rw [← he]; ring

omit [FiniteDimensional ℝ X] in
lemma day_exact (Z : Screen X) (hz : Z 0=0) (θ : ℝ) (ht : θ≠0) (x : X) :
    θ⁻¹^l • raw B Q (Z 0+θ • trim d Z θ x) = daylight B Q d Z θ x := by
  by_cases hh : l=0
  · exact (congr_arg _ (flat B Q hh ..)).trans ((smul_zero _).trans (flat B Q hh ..).symm)
  let v := trim d Z θ x
  rw [hz, zero_add]
  change _ • Cross.mix _ _ (θ • v.1) (θ • v.2) = _
  rw [map_smul, Cross.mix_degree,smul_smul,smul_smul,mul_assoc,← pow_succ',Nat.sub_add_cancel (Nat.pos_of_ne_zero hh),inv_pow,inv_mul_cancel₀ (pow_ne_zero l ht),one_smul] -- map_smul
  rfl

omit [FiniteDimensional ℝ X] in
lemma eve_exact (Z : Slides X) (hz : (Z 0).1=0) (θ χ : ℝ) (ht : θ≠0) (x : X) :
    θ⁻¹^l • ((χ*θ^2) • marked B Q (Z 0+θ • trim d Z θ x)) = evening B Q d Z θ χ x := by
  let v := trim d Z θ x
  let w := Z 0+θ • v
  have hw : w.1=θ • v.1 := by simp [w,hz]
  change θ⁻¹^l • ((χ*θ^2) • (Cross.rate B Q w.1 w.2.1 w.2.2.1 + Cross.mix B Q w.1 w.2.2.2))=
    χ • _
  rw [hw, Cross.rate_degree, Cross.mix_degree]
  simp_rw [smul_add]
  rw [scaled θ ht _ _ _ _ (by omega), scaled θ ht _ _ _ _ (by omega)]

/-- Exact coupons on k derivatives of energy or density insertions. Even
true at negative θ as long as nonzero. Smooth at θ=0 on RHS gives limit. -/
lemma cash (k : ℕ) (hk : k≤d+1) {Z : Screen X} (h : ContDiffAt ℝ ω Z 0) (hz : Z 0=0) {r : ℝ → X}
    (hr : ContDiff ℝ ω r) (he : r 0=0) {θ : ℝ} (ht : θ≠0) :
    iteratedDeriv k (fun t : ℝ => θ⁻¹^l • raw B Q (Z (θ • r t))) 0 =
      iteratedDeriv k (fun t : ℝ => daylight B Q d Z θ (r t)) 0 := by
  let P (p : X × X) := θ⁻¹^l • raw B Q p
  have hx := exchanged d hk θ h ((contDiff_const (c:=θ⁻¹^l)).smul (raw_smooth B Q) : ContDiff ℝ ω P) hr he
  simp_rw [← day_exact B Q d Z hz θ ht]; exact hx

lemma cash_div (k : ℕ) (hk : k≤d+1) {Z : Slides X} (h : ContDiffAt ℝ ω Z 0) (hz : (Z 0).1=0) {r : ℝ → X}
    (hr : ContDiff ℝ ω r) (he : r 0=0) {θ χ : ℝ} (ht : θ≠0) :
    iteratedDeriv k (fun t : ℝ => θ⁻¹^l • ((χ*θ^2) • marked B Q (Z (θ • r t)))) 0 =
      iteratedDeriv k (fun t : ℝ => evening B Q d Z θ χ (r t)) 0 := by
  let P (p : X × X × X × X) := θ⁻¹^l • ((χ*θ^2) • marked B Q p)
  have hx := exchanged d hk θ h ((contDiff_const (c:=θ⁻¹^l)).smul ((contDiff_const (c:=χ*θ^2)).smul (marked_smooth B Q)) : ContDiff ℝ ω P) hr he
  simp_rw [← eve_exact B Q d Z hz θ χ ht]; exact hx
end YM.ProjectorNext.Calibration.Coupon
