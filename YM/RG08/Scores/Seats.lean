import YM.RG08.Scores.Test
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Literal derivatives-of-measures interpretation

In the requested formal estimates eq:kme etc. Keep both signs;
carrier of every measure still the tested physical cell with the same D,
no completion by tests polynomial alone.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Scores
open Function Filter MeasureTheory Measure Set CompactlySupported
open scoped ENNReal Topology BigOperators

instance (D : ℕ) : MeasurableSpace (Sheet D) := borel _
instance (D : ℕ) : BorelSpace (Sheet D) := ⟨rfl⟩
instance (D : ℕ) : Nonempty (Sheet D) := ⟨⟨0,fun _=>0⟩⟩

abbrev Pin (D : ℕ) (R : ℝ) := Bool × Sheet D × Close R
def sign : Bool → ℝ := fun b => if b then -1 else 1

variable (D : ℕ) (R : ℝ)
def bill (x : Sight D R) : C(Pin D R,ℝ) := by
  refine ⟨fun i=> sign i.1 * (x.val i.2.1) i.2.2, ?_⟩
  refine ((continuous_of_discreteTopology (f:=sign)).comp continuous_fst).mul ?_
  fun_prop
private def post : ℝ×Sight D R →ₗ[ℝ] C(Pin D R,ℝ) where
  toFun i := ContinuousMap.const _ i.1 + bill D R i.2
  map_add' i j := by
    apply ContinuousMap.ext; intro x
    change i.1+j.1+(sign x.1)*(_+_)=(i.1+(sign x.1)*_) + (j.1+(sign x.1)*_); ring
  map_smul' c i := by
    apply ContinuousMap.ext; intro x
    change c*i.1+(sign x.1)*(c*_) = c*(i.1+(sign x.1)*_); ring
private lemma post_price (h : 0≤R) (c : ℝ × Sight D R) : ‖c.1‖+‖c.2‖ ≤ ‖post D R c‖ := by
  let T := ‖post D R c‖
  have he (k : Sheet D) (x : Close R) : ‖c.1‖+‖c.2.val k x‖≤T := by
    have h₁ := ContinuousMap.norm_coe_le_norm (post D R c) (false,k,x)
    have h₂ := ContinuousMap.norm_coe_le_norm (post D R c) (true,k,x)
    change ‖c.1+(sign false)*(c.2.val k x)‖ ≤ T at h₁
    change ‖c.1+(sign true)*(c.2.val k x)‖ ≤ T at h₂
    simp only [sign,Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul] at h₁ h₂
    rw [Real.norm_eq_abs,abs_le] at h₁ h₂
    simp only [Real.norm_eq_abs]; simp only [abs_eq_max_neg,max_def]; split <;> split <;> linarith
  let w₀ : Close R := ⟨0, fun i=>by simpa⟩
  have hh := he (Classical.arbitrary _) w₀
  have hV : 0 ≤ T-‖c.1‖ := by grw [← hh]; simp
  have hg : ‖c.2.val‖≤T-‖c.1‖ := (pi_norm_le_iff_of_nonneg hV).mpr fun i => (ContinuousMap.norm_le _ hV).mpr fun x => by linarith [he i x]
  change ‖c.1‖+‖c.2.val‖ ≤ T
  linarith

private def wanted (a : Voice D R) : ℝ×Sight D R →ₗ[ℝ] ℝ where
  toFun p := p.1*‖a‖+a p.2
  map_add' p q := by simp; ring
  map_smul' c p := by simp; ring
private lemma universal {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup M] [Module ℝ M] (q : M →ₗ[ℝ] E) (f : M→ₗ[ℝ]ℝ) {C : ℝ} (hc : 0≤C)
    (hp : ∀ x, ‖f x‖≤C*‖q x‖) : ∃ A : E→L[ℝ]ℝ,‖A‖≤C ∧ ∀ p,A (q p)=f p := by
  have hb : Surjective q.rangeRestrict := by rintro ⟨p,x,hx⟩; exact ⟨x,Subtype.ext hx⟩
  obtain ⟨w,hw,hW⟩:= port (E:=q.range) q.rangeRestrict hb f hc hp
  obtain ⟨A,hA,h⟩:= exists_extension_norm_eq q.range w
  exact ⟨A,h.le.trans hw,fun p => (hA (q.rangeRestrict p)).trans (LinearMap.congr_fun hW p)⟩


private lemma sells (h : 0≤R) (a : Voice D R) : ∃ A : C(Pin D R,ℝ) →L[ℝ] ℝ,
    ‖A‖≤‖a‖ ∧ ∀ p, A (post D R p)=wanted D R a p := by
  apply universal (E:=C(Pin D R,ℝ)) (M:=ℝ×Sight D R) (post D R) (wanted D R a) (norm_nonneg a)
  intro p
  change ‖p.1*‖a‖+a p.2‖ ≤ ‖a‖ * ‖post D R p‖
  apply (norm_add_le ..).trans; rw [norm_mul,norm_norm]
  grw [a.le_opNorm p.2,← post_price D R h p]; exact le_of_eq (by ring)

lemma receive (h : 0≤R) (a : Voice D R) : ∃ μ : Measure (Pin D R), IsFiniteMeasure μ ∧ μ.real univ=‖a‖ ∧
    ∀ t : Sight D R, a t=∫ x, bill D R t x ∂μ := by
  obtain ⟨A,hA,hw⟩:= sells D R h a
  have he (r) : A (ContinuousMap.const _ r)=r*‖a‖ := by
    have h := hw (r,0); rw [show post D R (r,0)=ContinuousMap.const _ r by ext x; change r+(sign _)*0=r; ring] at h
    change _ = r*‖a‖+a 0 at h; rw [map_zero,add_zero] at h; exact h
  have hp (f : C(Pin D R,ℝ)) (ht : ∀ x,0≤f x) : 0 ≤ A f := by
    let g : C(Pin D R,ℝ) := ContinuousMap.const _ ‖f‖ - f
    have hg : ‖g‖ ≤ ‖f‖ := (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun x=>by
      have hf := ContinuousMap.norm_coe_le_norm f x
      rw [Real.norm_eq_abs, abs_le] at hf
      change ‖‖f‖-f x‖ ≤ _; rw [Real.norm_eq_abs, abs_le]; have h := ht x; have h' := norm_nonneg f; constructor <;> linarith
    have hz : ‖A g‖ ≤ ‖a‖ * ‖f‖ := le_trans (A.le_opNorm g) (mul_le_mul hA hg (norm_nonneg _) (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_le] at hz
    have hx : A g=‖f‖*‖a‖-A f := (map_sub ..).trans (by rw [he]); rw [hx] at hz
    nlinarith only [hz.2]
  let M : C_c(Pin D R,ℝ) →ₚ[ℝ] ℝ := {
    toFun := fun f => A f.toContinuousMap
    map_add' := fun f g=>map_add A _ _
    map_smul' := fun c f=>map_smul A _ _
    monotone' := by
      intro f g hf
      rw [← sub_nonneg,←map_sub]
      exact hp _ fun i=>sub_nonneg.mpr (hf i) }
  let μ := RealRMK.rieszMeasure M
  have hX (f : C(Pin D R,ℝ)) : (∫ x, f x ∂μ)=A f := by
    let z : C_c(Pin D R,ℝ) := { toContinuousMap:= f,
                                 hasCompactSupport':= HasCompactSupport.of_compactSpace _ }
    exact RealRMK.integral_rieszMeasure _ z
  haveI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure M))
  refine ⟨μ,inferInstance,?_,fun t=>?_⟩
  · simpa [he] using (hX (ContinuousMap.const _ 1)).trans (he 1)
  rw [hX,← show post D R (0,t)=bill D R t by ext x; exact zero_add _,hw]; change a t=0*‖a‖ + a t; ring
end YM.RG08.Scores
