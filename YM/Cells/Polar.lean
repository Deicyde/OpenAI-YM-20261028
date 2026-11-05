import YM.Cells.Copies

/-!
# Check PSD port gives dissemination bounds (one cut)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells
open Function Set Filter MeasureTheory
open Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder ComplexConjugate

/-- A two-input Hermitian form estimate, include vanishing diag. -/
theorem schwarz {a b z : ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (H : ∀ t : ℂ, 0 ≤ a + star t*z+t*(star z) + t*(star t)*b) : ‖z‖^2 ≤ ‖a‖*‖b‖ := by
  set A := a.re
  set B := b.re
  set R := Complex.normSq z
  have hp : 0 ≤ A := ha.1
  have hq : 0 ≤ B := hb.1
  have hR : 0 ≤ R := Complex.normSq_nonneg _
  have he : a = (A:ℂ) := Complex.ext rfl ha.2.symm
  have hx : b = (B:ℂ) := Complex.ext rfl hb.2.symm
  have hh (r : ℝ) : 0 ≤ A - 2 * r * R + r * r * R * B := by
    let c := (r : ℂ)
    specialize H (-c*z)
    rw [he,hx,show (A:ℂ) + _ + _ + _ = ((A-2*r*R+r*r*R*B : ℝ) : ℂ) by
      have hg : star z * z = (R:ℂ) := by rw [mul_comm]; exact Complex.mul_conj z
      push_cast; rw [← hg]; simp only [star_mul',c, star_neg, Complex.star_def, Complex.conj_ofReal]
      ring] at H
    exact H.1
  rw [sq,Complex.norm_mul_self_eq_normSq,he,hx]
  simp only [Complex.norm_real,Real.norm_of_nonneg hp,Real.norm_of_nonneg hq]
  change R ≤ A*B
  rcases eq_or_lt_of_le hq with hk|hk
  · rw [← hk,mul_zero]
    by_contra! hv
    specialize hh ((A+1)/R)
    rw [← hk] at hh
    field_simp at hh; nlinarith
  specialize hh B⁻¹
  field_simp at hh; nlinarith

variable {n : Side} {G : Gauge} {β : ℝ} {C : Cut n}
variable {P Q A : Config G n → ℂ}

/-- Linear in first (Cauchy Schwarz uses only norms). -/
def form (β : ℝ) (C : Cut n) (P Q : Config G n → ℂ) :=
  moment β fun U => P U * star (Q (C.pullC G U))

lemma form_int (hp : Interior C.sector P) (hq : Interior C.sector Q) (β : ℝ) :
    Integrable (fun U => P U * star (Q (C.pullC G U))) (law G n β) :=
  ((hp.enlarges (subset_univ _)).times ((hq.unchanged C.flip C.slide (mapsTo_univ ..)).real)).integrable _

lemma exchange (hp : Interior C.sector P) (hq : Interior C.sector Q) : form β C P Q = star (form β C Q P) := by
  rw [form,← moment_pull _ C.flip C.slide _ (form_int hp hq _)]
  unfold form moment
  rw [Complex.star_def, ← integral_conj]; apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_; simp only [Function.comp_apply]
  change P (C.pullC G x) * star (Q (C.pullC G (C.pullC G x))) = star _
  simp [mul_comm]

lemma plusF (hp : Interior C.sector P) (hq : Interior C.sector Q) (ha : Interior C.sector A) :
    form β C (fun U => P U + Q U) A = form β C P A + form β C Q A := by
  simp_rw [form,moment,add_mul,integral_add (form_int hp ha _) (form_int hq ha _)]

lemma scaleF (t : ℂ) : form β C (fun U => t*P U) A = t * form β C P A := by
  simp_rw [form,moment,mul_assoc, integral_const_mul]

lemma cauchy (H : Positive G β C) (hp : Interior C.sector P) (hq : Interior C.sector Q) :
    ‖form β C P Q‖^2 ≤ ‖form β C P P‖ * ‖form β C Q Q‖ := by
  apply schwarz (H P hp) (H Q hq)
  intro t
  let v := fun U => P U + t * Q U
  have hu : Interior C.sector (fun U => t * Q U) := hq.scale t
  have he : Interior C.sector v := hp.plus hu
  have hh (x : Config G n → ℂ) (hx : Interior C.sector x) : form β C x v = form β C x P + star t * form β C x Q := by
    rw [exchange hx he]
    unfold v
    rw [plusF hp hu hx,scaleF (P := Q)]
    simp only [star_add,star_mul']
    rw [← exchange hx hp,← exchange hx hq]
  have hv := plusF (β := β) hp hu he
  have hB : form β C v v = _ := hv
  rw [hh P hp,scaleF,hh Q hq,exchange hq hp] at hB
  exact (show 0 ≤ form β C v v from H v he).trans_eq (hB.trans (by unfold form; ring))

namespace Tiling
variable (T : Tiling n)

abbrev rootPower (β : ℝ) (F : T.Cell → Config G n → ℂ) : ℝ := ‖moment β (T.fullAt F)‖

/-- The fold estimate, *actual* orientations on all cells. -/
theorem fold_both (p a) (h : Positive G β (T.bandCut p a))
    (f g : T.Cell → Config G n → ℂ) (hf : ∀ i, Interior (T.chamber 0) (f i)) (hg : ∀ i, Interior (T.chamber 0) (g i)) :
    (T.rootPower β (T.assign p a f g))^2 ≤ T.rootPower β (T.assign p a f f) * T.rootPower β (T.assign p a g g) := by
  have hP (f g : T.Cell → Config G n → ℂ) : T.rootPower β (T.assign p a f g) =
      ‖form β (T.bandCut p a) (T.Part p a f) (T.Part p a g)‖ := by
    unfold form rootPower
    rw [← funext (T.reflect_equation p a f g)]
  rw [hP, hP,hP]
  exact cauchy h (T.partInterior p a _ hf) (T.partInterior p a _ hg)
end Tiling
end YM.Cells
