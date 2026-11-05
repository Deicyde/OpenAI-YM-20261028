import YM.Next.FOUNDATIONS.Reorient
import YM.Next.FOUNDATIONS.Split
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Sides
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Weights

/-!
# Conjugation and scalar prices of Coefficient movement

For the literal representations. No star on the tests hidden in the formula
for `.density` of a source. Vacuum/K reads are real. No replacement of
varkappa or schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Labels Lattice Wilson RG Source Analysis MeasureTheory Next.Foundations
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d}
    {Q : Coefficient F n} {R : Rep G n} {o : Site n} {H : Hol G}

/-- Doesn't move the indices. -/
def pigment (Q : Coefficient F n) : Coefficient F n := ⟨star Q.x,Q.support,star Q.regular,star Q.forced⟩

lemma pigment_format (h : Q.Format o H R) : (pigment Q).Format o H R := by
  let s := R.p
  constructor
  · intro i
    let P := Q.support i; let f := Q.regular i
    have hi : s.Regular P f := h.smooth i
    have hh (U) (hu : Healthy s.threshold P U) : HasOrderAt (star f) U s.order :=
      (starL' ℝ (A:=ℂ)).toContinuousLinearMap.contDiff.contDiffAt.comp 0 (hi.smooth U hu)
    refine ⟨fun U V h => congr_arg star (hi.sites U V h),continuous_star.measurable.comp hi.borel,
      fun k U => congr_arg star (hi.symmetry k U),hh,fun U hu A l he => left_has _ he (hh U hu)⟩
  · exact h.origin
  · intro i; change star (Q.regular i 1) = _; rw [h.identity_null,star_zero]
  · intro i ha
    have he : Reads H o (Q.support i) (0:Label G d) (Q.regular i) :=
      (reads_null_iff ..).mpr ⟨h.identity_null i,h.projects i⟩
    have hx := reads_bar he; rw [map_zero] at hx; exact ((reads_null_iff ..).mp hx).2 ha
  · intro i U hu; refine h.forcing i U fun e => hu ?_; simp only [pigment,Pi.star_apply,e,star_zero]
  · intro i hu; refine h.carried i fun e => hu ?_; change star (Q.forced i) = _; rw [e,star_zero]
  · exact fun i k U => congr_arg star (h.invariant i k U)
  · exact fun i U V h1 h2 => congr_arg star (h.supported i U V h1 h2)
  exact fun i => continuous_star.measurable.comp (h.borel i)

lemma pigment_cap {v c : ℝ} (h : Q.remBound o R v c) : (pigment Q).remBound o R v c := by
  obtain ⟨a,g,ha,hg,hc,hv,⟨E,hE,hX⟩,⟨B,hB,hY⟩⟩ := h
  refine ⟨a,g,ha,hg,hc,hv,⟨E,hE,?_⟩,B,hB,?_⟩
  · intro i
    have he (l) (U) : leftDerivs (star (Q.regular i)) l U = star (leftDerivs (Q.regular i) l U) := by
      induction l generalizing U with
      | nil => rfl
      | cons x l ih => simp only [leftDerivs,ih]; exact deriv.star
    refine ⟨(hX i).1,fun U hu l hl hs => ?_⟩; change ‖leftDerivs (star (Q.regular i)) l U‖ ≤ _
    rw [he,norm_star]; exact (hX i).2 U hu l hl hs
  refine fun i => ⟨(hY i).1,fun U => ?_⟩
  change ‖star (Q.forced i U)‖ ≤ _; rw [norm_star]; exact (hY i).2 U

lemma mask_star (s : ℝ) (B : Support n) (f : Config G n → ℂ) :
    masked s B (star f) = star (masked s B f) := by
  funext U; rw [Pi.star_apply]
  by_cases he : Healthy s B U <;> simp [he]

lemma pigment_density (S : SectionData F) (h : S.Sound H) (o : Site n) :
    (pigment Q).density o S R = star (Q.density o S R) := by
  classical
  let P := pigment Q
  have hr (x : F.Coeff) : F.core (star x) = star (F.core x) := by
    funext i; by_cases hi : i=0 <;> simp [Frame.core, Function.update, hi]
  funext U
  have he : P.exponentialEntry o S R U = star (Q.exponentialEntry o S R U) := by
    unfold Coefficient.exponentialEntry
    have ht (i) : P.maskedTerm R i U = star (Q.maskedTerm R i U) := congr_fun (mask_star ..) U
    have hx (x : F.Coeff) : S.places (star x) o = star (S.places x o) := funext fun V => h.ordinary_real _ _
    rw [star_add,tsum_star]; simp_rw [ht]; congr 1
    change star (Q.x 0) + masked _ _ (S.places _ o) U = star (_+_)
    rw [show P.x = star Q.x from rfl, hr,scaled_bar,hx, mask_star, star_add]; rfl
  have hk (i) : P.marked R i U = star (Q.marked R i U) := by
    unfold Coefficient.marked; split
    · rw [star_sum]; refine Finset.sum_congr rfl fun j hj => ?_; simp [P,pigment]
    rw [star_zero]
  rw [Pi.star_apply]
  change P.density _ _ _ _ = _
  unfold Coefficient.density
  rw [he]; simp_rw [hk]; rw [← tsum_star]
  have ht (x : ℝ) : star (x : ℂ) = ↑x := by simp
  rw [star_add,star_mul,star_mul,ht,ht]; ring

/-- Charge the given scalar. -/
def repaint (a : ℂ) (Q : Coefficient F n) : Coefficient F n := ⟨a • Q.x,Q.support,a • Q.regular,a • Q.forced⟩

lemma paint_format (a : ℂ) (h : Q.Format o H R) : (repaint a Q).Format o H R := by
  constructor
  · exact fun i => regular_smul a (h.smooth i)
  · exact h.origin
  · intro i; change a • (Q.regular i 1) = _; rw [h.identity_null,smul_zero]
  · intro i ha J
    let g := fun x => Q.regular i (H.testLinks d o J x)
    have he := h.projects i ha J
    refine ⟨ContDiffAt.const_smul (f:=g) a he.1, fun k hk => ?_⟩
    change iteratedDeriv k (a • g) 0 = 0
    rw [iteratedDeriv_const_smul _ a,show iteratedDeriv k g 0 = 0 from he.2 k hk,smul_zero]
    exact (show ContDiffAt ℝ (d : WithTop ℕ∞) g 0 from he.1).of_le (Nat.cast_le.mpr hk)
  · intro i U hu; refine h.forcing i U fun e => hu ?_; change a • (Q.forced i U) = _; rw [e,smul_zero]
  · intro i hu; refine h.carried i fun e => hu ?_; change a • Q.forced i = _; rw [e,smul_zero]
  · exact fun i k U => congr_arg (a • ·) (h.invariant i k U)
  · exact fun i U V h1 h2 => congr_arg (a • ·) (h.supported i U V h1 h2)
  exact fun i => (h.borel i).const_smul a

lemma paint_cap (a : ℂ) {v c : ℝ} (h : Q.remBound o R v c) : (repaint a Q).remBound o R v (‖a‖*c) := by
  obtain ⟨r,g,ha,hg,hc,hv,⟨E,hE,hX⟩,⟨B,hB,hY⟩⟩ := h
  have he (Q : ℕ → Support n) (M : ℕ → ℝ) (b : ℝ) (ht : SumBudget (fun i => R.p.mass (Q i) (M i)) b) :
      SumBudget (fun i => R.p.mass (Q i) (‖a‖*M i)) (‖a‖*b) := by
    have hp (i) : R.p.mass (Q i) (‖a‖*M i) = ‖a‖ * R.p.mass (Q i) (M i) := by unfold BudgetPoint.mass; ring
    simp_rw [hp]; refine ⟨fun i => mul_nonneg (norm_nonneg _) (ht.1 i), ht.2.1.mul_left _,?_⟩
    rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left ht.2.2 (norm_nonneg _)
  refine ⟨‖a‖*r,‖a‖*g,mul_nonneg (norm_nonneg _) ha,mul_nonneg (norm_nonneg _) hg,?_,hv,
    ⟨fun i => ‖a‖*E i,he _ _ r hE,fun i => bound_smul _ (hX i)⟩,fun i => ‖a‖*B i,?_,?_⟩
  · rw [← mul_add]; exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)
  · rw [mul_left_comm]; exact he _ _ _ hB
  refine fun i => ⟨mul_nonneg (norm_nonneg _) (hY i).1,fun U => ?_⟩
  change ‖a • Q.forced i U‖ ≤ _; rw [norm_smul]; exact mul_le_mul_of_nonneg_left ((hY i).2 U) (norm_nonneg _)

lemma mask_paint (s : ℝ) (a : ℂ) (B : Support n) (f : Config G n → ℂ) : masked s B (a • f) = a • masked s B f := by
  funext U; rw [Pi.smul_apply]; by_cases he : Healthy s B U <;> simp [he]

lemma paint_density (a : ℂ) (S : SectionData F) (o : Site n) :
    (repaint a Q).density o S R = a • Q.density o S R := by
  classical
  funext U
  let P := repaint a Q
  have he : P.exponentialEntry o S R U = a • Q.exponentialEntry o S R U := by
    unfold Coefficient.exponentialEntry; rw [smul_add]
    have ht (i) : P.maskedTerm R i U = a • Q.maskedTerm R i U := congr_fun (mask_paint ..) U
    simp_rw [ht]; rw [show ∑' i, a • Q.maskedTerm R i U = a • ∑' i, Q.maskedTerm R i U from tsum_mul_left]; congr 1
    have hp (x : F.Coeff) : S.places (a • x) o = a • S.places x o := funext fun U =>
      congr_fun (S.eval_linear.map_smul a x) (expandAt o U)
    rw [smul_add,show P.x = a • Q.x from rfl,map_smul,map_smul,hp,mask_paint]; rfl
  have hk (i) : P.marked R i U = a • Q.marked R i U := by
    unfold Coefficient.marked; split
    · rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => mul_assoc ..
    rw [smul_zero]
  rw [Pi.smul_apply]; change P.density _ _ _ _ = _
  unfold Coefficient.density; rw [he]; simp_rw [hk]; simp only [smul_eq_mul,tsum_mul_left]; ring
end YM.ProjectorNext.Equivariance
