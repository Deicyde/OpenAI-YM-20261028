import YM.Push.STRESS_FLUX.LinkD
import YM.Work.A15
import YM.Work.C13.Decay

/-!
Haar-Wilson Ward identity, including contact terms on the genuine probability measure.
No assumption that arbitrary coordinate changes preserve the *weighted* measure or that a
field-dependent link variation has zero divergence. Coefficients depending on transports
(in particular from negative link reads) must also be differentiated. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Function Set Gauge Lattice Wilson MeasureTheory Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side}

structure Tame (f : Config G n → ℂ) : Prop where
  meas : Measurable f
  bounded : ∃ C : ℝ, 0≤C ∧ ∀ U, ‖f U‖ ≤ C

variable {f g : Config G n → ℂ} {x : Site n} {d : Step} {c : G.Color}
lemma tame_of_continuous (hf : Continuous f) : Tame f := by
  obtain ⟨C,hC⟩ := (isCompact_range hf.norm).bddAbove
  exact ⟨hf.measurable, C, (norm_nonneg _).trans (hC (mem_range_self (1:Config G n))),fun U => hC (mem_range_self U)⟩
lemma Tame.int (hf : Tame f) (μ : Measure (Config G n)) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C,-,hC⟩ := hf.bounded; exact Integrable.of_bound hf.meas.aestronglyMeasurable C (.of_forall hC)
lemma Tame.mul (hf : Tame f) (hg : Tame g) : Tame (fun U => f U * g U) := by
  obtain ⟨a,ha,H⟩ := hf.bounded; obtain ⟨b,hb,h⟩ := hg.bounded
  exact ⟨hf.meas.mul hg.meas,a*b,by positivity,fun U => by rw [norm_mul]; exact mul_le_mul (H _) (h _) (norm_nonneg _) ha⟩
lemma Tame.add (hf : Tame f) (hg : Tame g) : Tame (fun U => f U + g U) := by
  obtain ⟨a,ha,H⟩ := hf.bounded; obtain ⟨b,hb,h⟩ := hg.bounded
  exact ⟨hf.meas.add hg.meas,a+b,add_nonneg ha hb,fun U => (norm_add_le ..).trans (add_le_add (H _) (h _))⟩
lemma Tame.sub (hf : Tame f) (hg : Tame g) : Tame (fun U => f U - g U) := by
  obtain ⟨a,ha,H⟩ := hf.bounded; obtain ⟨b,hb,h⟩ := hg.bounded
  exact ⟨hf.meas.sub hg.meas,a+b,add_nonneg ha hb,fun U => (norm_sub_le ..).trans (add_le_add (H _) (h _))⟩
lemma Tame.post (hf : Tame f) (L : ℂ →L[ℝ] ℂ) :
    Tame (fun U => L (f U)) := by
  obtain ⟨a,ha,H⟩ := hf.bounded
  exact ⟨L.continuous.measurable.comp hf.meas, ‖L‖ * a, by positivity, fun U => L.le_of_opNorm_le_of_le le_rfl (H U)⟩


structure Varies (x : Site n) (d : Step) (c : G.Color) (f : Config G n → ℂ) : Prop where
  tame : Tame f
  slope : Tame (Dlink x d c f)
  has (U : Config G n) : HasDerivAt (fun t => f (bump x d c t U)) (Dlink x d c f U) 0
lemma Varies.atTime (h : Varies x d c f) (U : Config G n) (t : ℝ) : HasDerivAt (fun s => f (bump x d c s U))
    (Dlink x d c f (bump x d c t U)) t := bump_deriv x d c (h.has _)
lemma RegularD.varies (h : RegularD f) : Varies x d c f := ⟨tame_of_continuous h.cont,tame_of_continuous (h.contD ..), fun U => h.has x d U c⟩
lemma Varies.of_off (h : Tame f) (hf : ∀ U t, f (bump x d c t U)=f U) : Varies x d c f := by
  refine ⟨h,?_,fun U => ?_⟩
  · apply tame_of_continuous; change Continuous fun U => Dlink ..; simp_rw [Dlink, hf, deriv_const]; exact continuous_const
  simp_rw [Dlink, hf, deriv_const]; exact hasDerivAt_const ..
lemma Varies.localOn (h : Tame f) {B : Set (Site n)} (hb : LocalOn B f) (hx : x∉B ∨ x+d.vec∉B) : Varies x d c f := by
  apply Varies.of_off h (fun U t => hb _ _ ?_); intro i hi hI
  have hq : i ≠ d.used x := by rintro rfl; unfold Step.used at hi hI; unfold Step.vec at hx; split at hi <;> simp_all [← sub_eq_add_neg]
  unfold bump modify; rw [if_neg hq]

lemma Varies.Dmul (h : Varies x d c f) (hq : Varies x d c g) (U) : Dlink x d c (fun U => f U * g U) U = Dlink x d c f U * g U + f U * Dlink x d c g U := by
  simpa only [Dlink,bump_zero] using! ((h.has U).fun_mul (hq.has U)).deriv
lemma Varies.mul (h : Varies x d c f) (hq : Varies x d c g) : Varies x d c (fun U => f U*g U) := by
  refine ⟨h.tame.mul hq.tame,?_,fun U => ?_⟩
  · rw [funext (h.Dmul hq)]; exact (h.slope.mul hq.tame).add (h.tame.mul hq.slope)
  exact ((h.has U).fun_mul (hq.has U)).differentiableAt.hasDerivAt

/-- Unnormalized Haar integral (probability Haar prior; does not forget spectator
contact derivatives). Regularity only needed in one direction. -/
theorem haar_deriv (h : Varies x d c f) : ∫ U, Dlink x d c f U ∂prior G n = 0 := by
  let μ := prior G n
  let F (t : ℝ) U := f (bump x d c t U)
  have hF (t) : Measurable (F t) := h.tame.meas.comp (continuous_modify ..).measurable
  have he t : ∫ U, F t U ∂μ = ∫ U, f U ∂μ := by
    have he := prior_modify x d (G.lieExp (t • c))
    have hp := integral_map (μ:=μ) (φ:=bump x d c t) (f:=f) he.measurable.aemeasurable h.tame.meas.aestronglyMeasurable
    rw [show Measure.map (bump x d c t) μ=μ from he.map_eq] at hp; exact hp.symm
  let A (t : ℝ) U := Dlink x d c f (bump x d c t U)
  obtain ⟨C,hC,hb⟩ := h.slope.bounded
  obtain ⟨-,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) (F:=F) (x₀:=0) (F':=A) (bound:=fun _ => C)
    (s:=univ) univ_mem (.of_forall (fun t => (hF t).aestronglyMeasurable)) (by simpa [F] using h.tame.int μ)
    (by simpa [A] using h.slope.meas.aestronglyMeasurable) (.of_forall (fun U t _ => hb _)) (integrable_const _)
    (.of_forall (fun U t _ => h.atTime U t))
  simp only [A,bump_zero,he] at hd; exact hd.unique (hasDerivAt_const ..)

abbrev bill (β : ℝ) (U : Config G n) : ℂ := (bare β U : ℝ)
lemma bare_varies (β : ℝ) : Varies x d c (bill β) := by
  have ht (U : Config G n) : HasDerivAt (fun t => bill β (bump x d c t U))
      (bill β U * ((↑(-β * ⟪c,force U x d⟫_ℝ) : ℂ))) 0 := by
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (bare_variation β x d c 0 U)).congr_deriv (by simp [Complex.ofReal_mul])
  have he U := (ht U).deriv
  refine ⟨tame_of_continuous (Complex.continuous_ofReal.comp (bare_cont β)),tame_of_continuous ?_,fun U => (ht U).differentiableAt.hasDerivAt⟩
  rw [show Dlink x d c (bill β) = _ from funext he]; unfold bill; fun_prop

private def cost (x : Site n) (d : Step) (c : G.Color) (U : Config G n) : ℂ := ⟪c,force U x d⟫_ℝ
@[fun_prop] lemma continuous_cost (x : Site n) (d : Step) (c : G.Color) : Continuous (cost x d c) := by unfold cost; fun_prop

/-- Finite change of variables on the actual normalized Wilson law, including β and
all insertions inside f. No division by β needed. Includes every finite period and β=0. -/
theorem wilson_deriv (h : Varies x d c f) (β : ℝ) :
    moment β (fun U => (↑(β * ⟪c,force U x d⟫_ℝ) : ℂ) * f U) = moment β (Dlink x d c f) := by
  have hc : Continuous (fun U => (↑(β * ⟪c,force U x d⟫_ℝ) : ℂ)) := by fun_prop
  have hP := (tame_of_continuous hc).mul h.tame
  have hf : Tame (bill (G:=G) (n:=n) β) := (tame_of_continuous (Complex.continuous_ofReal.comp (bare_cont β) : Continuous (bill (G:=G) (n:=n) β)))
  have he (U : Config G n) : Dlink x d c (bill β) U = -bill β U * ↑(β * ⟪c,force U x d⟫_ℝ) := by
    have ht := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (bare_variation β x d c 0 U)).deriv
    change Dlink x d c (bill β) U = (↑(bare β _ * (_ * _) : ℝ) : ℂ) at ht
    rw [ht, bump_zero,Complex.ofReal_mul, neg_mul,Complex.ofReal_neg,neg_mul,mul_neg]
  have hp (U) : Dlink x d c (fun V => bill β V * f V) U =
      bill β U * Dlink x d c f U - bill β U * (↑(β * ⟪c,force U x d⟫_ℝ) * f U) := by rw [(bare_varies β).Dmul h, he]; ring
  rw [moment_formula _ _ (hP.int _),moment_formula _ _ (h.slope.int _)]; congr 1
  have hl := haar_deriv ((bare_varies β).mul h)
  rw [funext hp, integral_sub ((hf.mul h.slope).int _) ((hf.mul hP).int _)] at hl
  exact (sub_eq_zero.mp hl).symm

/-- Scalar-weighted direction, normalized equation insertion at βG − div scale. -/
def insertion (β : ℝ) (x : Site n) (d : Step) (c : G.Color) (g : Config G n → ℂ) U :=
    (↑(β * ⟪c,force U x d⟫_ℝ) : ℂ)*g U - Dlink x d c g U

lemma Varies.tameInsertion (h : Varies x d c g) (β : ℝ) : Tame (insertion β x d c g) :=
    ((tame_of_continuous (show Continuous (fun U => (↑(β * ⟪c,force U x d⟫_ℝ) : ℂ)) by fun_prop)).mul h.tame).sub h.slope

theorem insertion_moment (h : Varies x d c g) (hf : Varies x d c f) (β : ℝ) :
    moment β (fun U => insertion β x d c g U * f U) = moment β (fun U => g U * Dlink x d c f U) := by
  have ht := wilson_deriv (h.mul hf) β
  unfold moment at *
  simp_rw [h.Dmul hf] at ht
  simp_rw [integral_add ((h.slope.mul hf.tame).int _) ((h.tame.mul hf.slope).int _)] at ht
  have hc : Continuous (fun U => (↑(β * ⟪c,force U x d⟫_ℝ) : ℂ)) := by fun_prop
  simp_rw [insertion, sub_mul, mul_assoc, integral_sub (((tame_of_continuous hc).mul (h.tame.mul hf.tame)).int _) ((h.slope.mul hf.tame).int _),ht,add_sub_cancel_left]

abbrev orth (i : G.ColorIndex) : G.Color := (EuclideanSpace.basisFun _ ℝ) i

lemma orth_inner (x : G.Color) (i : G.ColorIndex) : ⟪orth i, x⟫_ℝ = x i := by simp [orth, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

def divLink (x : Site n) (d : Step) (X : Config G n → G.Color) U := ∑ i : G.ColorIndex, Dlink x d (orth i) X U i



@[fun_prop] theorem continuous_divLink (x : Site n) (d : Step) {X : Config G n → G.Color} (hX : RegularD X) : Continuous (divLink x d X) := by
  unfold divLink; fun_prop (disch:=assumption)

def equation (β : ℝ) (x : Site n) (d : Step) (X : Config G n → G.Color) (U : Config G n) := β * ⟪X U,force U x d⟫_ℝ - divLink x d X U




abbrev paint (X : Config G n → G.Color) (i : G.ColorIndex) (U : Config G n) := (↑(X U i) : ℂ)
lemma regular_paint {X : Config G n → G.Color} (i : G.ColorIndex) (h : RegularD X) : RegularD (paint X i) := h.post (Complex.ofRealCLM.comp (EuclideanSpace.proj i))
lemma D_paint (x : Site n) (d : Step) (c : G.Color) (U : Config G n) (i : G.ColorIndex) {X : Config G n → G.Color} (h : RegularD X) :
    Dlink x d c (paint X i) U = ↑(Dlink x d c X U i) := ((Complex.ofRealCLM.comp (EuclideanSpace.proj i)).hasFDerivAt.comp_hasDerivAt 0 (h.has x d U c)).deriv
lemma insertion_sum (β : ℝ) (x : Site n) (d : Step) {X : Config G n → G.Color} (hX : RegularD X) (U : Config G n) :
    ∑ i, insertion β x d (orth i) (paint X i) U = (equation β x d X U : ℂ) := by
  have h : ∀ i, ↑(β * ⟪orth i,force U x d⟫_ℝ) * paint X i U = ((β * (X U i * force U x d i) : ℝ):ℂ) := by
    intro i; rw [orth_inner]; push_cast; unfold paint; ring
  simp only [insertion, equation, h, D_paint x d _ U _ hX,Finset.sum_sub_distrib, ← Complex.ofReal_sum, ← Finset.mul_sum]
  rw [← Complex.ofReal_sub]; congr 2
  simp only [real_inner_comm (force U x d), EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,Finset.mul_sum]


def contact (x : Site n) (d : Step) (X : Config G n → G.Color) (f : Config G n → ℂ) U := ∑ i, paint X i U * Dlink x d (orth i) f U


/-- Change-of-variables identity for a vector field in physical color coordinates; complex
extension by linear combinations, β nonzero for the inverse-β version. -/
theorem equation_moment (β : ℝ) {X : Config G n → G.Color} (hX : RegularD X) (hf : ∀ i, Varies x d (orth i) f) :
    moment β (fun U => ↑(equation β x d X U) * f U) = moment β (contact x d X f) := by
  simp_rw [← insertion_sum β _ d hX, Finset.sum_mul,moment,contact,
    integral_finsetSum _ (fun i _ => (((regular_paint i hX).varies.tameInsertion β).mul (hf i).tame).int _),
    integral_finsetSum _ (fun i _ => ((tame_of_continuous (regular_paint i hX).cont).mul (hf i).slope).int _)]
  exact Finset.sum_congr rfl fun i _ => insertion_moment (regular_paint i hX).varies (hf i) β
lemma equation_continuous (β : ℝ) (x : Site n) (d : Step) {X : Config G n → G.Color} (hX : RegularD X) : Continuous (equation β x d X) :=
  (continuous_const.mul (hX.cont.inner (𝕜:=ℝ) (force_cont ..))).sub (continuous_divLink x d hX)


theorem haar_nullity (β : ℝ) {X : Config G n → G.Color} (hX : RegularD X) (h : Tame f) {B : Set (Site n)} (hb : LocalOn B f) (he : x∉B ∨ x+d.vec∉B) :
    moment β (fun U => ↑(equation β x d X U) * f U) = 0 := by
  rw [equation_moment β hX (fun _ => Varies.localOn h hb he)]; simp [moment, contact, Dlink_off hb he]
end YM.StressFlux
