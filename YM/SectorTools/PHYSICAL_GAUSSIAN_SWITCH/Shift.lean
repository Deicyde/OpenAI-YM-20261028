import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Trade

/-!
# L¹ identity and Lp comparison as normalized laws of physical coordinates
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment.Relative (trade)
open scoped Topology BigOperators ENNReal
local notation "Covar" => Next.SectorChange.Gaussian.Table

variable {I : Type} [Fintype I] [DecidableEq I]

def shift (C : Covar I) (m : Vec I) := (cloud C).map (fun z => m+z)

lemma to_shift (C : Covar I) (m : Vec I) :
    MeasurePreserving (MeasurableEquiv.addLeft m) (cloud C) (shift C m) :=
  ⟨by fun_prop,rfl⟩

lemma shift_probability (C : Covar I) (m : Vec I) : IsProbabilityMeasure (shift C m) :=
  Measure.isProbabilityMeasure_map (show AEMeasurable (fun z : Vec I => m+z) (cloud C) by fun_prop)
attribute [local instance] shift_probability

lemma centered (C : Covar I) : shift C 0 = cloud C := by unfold shift; simp

variable {A D : Covar I} {a d : Vec I} {p : ℝ}
/-- Target `shift A a` against `shift D d`, common absolute address x. -/
def likelihood (A : Covar I) (a : Vec I) (D : Covar I) (d x : Vec I) := trade A D (d-a) (x-d)
lemma like_pos (hA : A.PosDef) (hD : D.PosDef) (a d x : Vec I) : 0 < likelihood A a D d x := trade_pos hA hD ..
lemma like_cont (A : Covar I) (a : Vec I) (D : Covar I) (d : Vec I) : Continuous (likelihood A a D d) :=
  (trade_cont ..).comp (continuous_id.sub continuous_const)
lemma like_meas (A : Covar I) (a : Vec I) (D : Covar I) (d : Vec I) : Measurable (likelihood A a D d) := (like_cont ..).measurable
lemma likeref (A : Covar I) (a : Vec I) (D : Covar I) (d z : Vec I) : likelihood A a D d (d+z) = trade A D (d-a) z := by rw [likelihood, add_sub_cancel_left]

section expectations
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
lemma shift_int (C : Covar I) (m : Vec I) (f : Vec I → X) :
    (Integrable f (shift C m) ↔ Integrable (fun z => f (m+z)) (cloud C)) ∧
    (∫ x,f x ∂shift C m) = ∫ z,f (m+z) ∂cloud C :=
  ⟨((to_shift C m).integrable_comp_emb (MeasurableEquiv.addLeft m).measurableEmbedding).symm,
    ((to_shift C m).integral_comp' f).symm⟩

lemma shift_identity (hA : A.PosDef) (hD : D.PosDef) (a d : Vec I) (f : Vec I → X) :
    (Integrable f (shift A a) ↔ Integrable (fun x => likelihood A a D d x • f x) (shift D d)) ∧
      (∫ x,f x ∂shift A a)=∫ x,likelihood A a D d x • f x ∂shift D d := by
  rw [(shift_int A a f).1,(shift_int A a f).2,(shift_int D d _).1,(shift_int D d _).2]
  simp_rw [likeref]
  have he (z : Vec I) : a+(d-a+z)=d+z := by abel
  simpa only [he] using AnalyticBridge.GaussianFieldAlignment.Relative.change hA hD (d-a) (fun z => f (a+z))
end expectations

lemma like_mean (hA : A.PosDef) (hD : D.PosDef) :
    Integrable (likelihood A a D d) (shift D d) ∧ (∫ x,likelihood A a D d x ∂shift D d)=1 := by
  rw [(shift_int ..).1, (shift_int ..).2]; simp_rw [likeref]; exact normalized_trade hA hD _

/-- Equality of measures, not just a formal quotient of expressions in the
exponent. -/
theorem with_likelihood (hA : A.PosDef) (hD : D.PosDef) :
    (shift D d).withDensity (fun x => ENNReal.ofReal (likelihood A a D d x)) = shift A a := by
  let μ := shift D d; let ν := shift A a; let f := likelihood A a D d
  change μ.withDensity _ = ν
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs]
  have ht : Integrable f (μ.restrict s) := (like_mean hA hD).1.integrableOn
  rw [← ofReal_integral_eq_lintegral_ofReal ht (Eventually.of_forall fun x => (like_pos hA hD a d x).le)]
  have he := (shift_identity hA hD a d (s.indicator (1 : Vec I → ℝ))).2
  rw [integral_indicator_one hs] at he
  have hh (x : Vec I) : f x • s.indicator (1 : Vec I → ℝ) x = s.indicator f x := by by_cases x∈s <;> simp [*]
  change ν.real s = ∫ x,f x • s.indicator (1 : Vec I → ℝ) x ∂μ at he
  simp_rw [hh,integral_indicator hs] at he
  haveI : IsProbabilityMeasure ν := shift_probability ..
  rw [← he, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top ν s)]

theorem likelihood_deriv (hA : A.PosDef) (hD : D.PosDef) :
    (shift A a).rnDeriv (shift D d) =ᵐ[shift D d] fun x => ENNReal.ofReal (likelihood A a D d x) := by
  rw [← with_likelihood (d:=d) hA hD]
  exact Measure.rnDeriv_withDensity _ (like_meas ..).ennreal_ofReal

lemma like_integrable_iff (hA : A.PosDef) (hD : D.PosDef) :
    Integrable (fun x => likelihood A a D d x ^ p) (shift D d) ↔ (mixed A D p).PosDef := by
  rw [(shift_int ..).1]; simp_rw [likeref]; exact trade_integrable_iff hA hD


theorem like_integral (hA : A.PosDef) (hD : D.PosDef) (he : (mixed A D p).PosDef) :
    (∫ x, likelihood A a D d x ^ p ∂ shift D d) = price A D p (d-a) := by
  rw [(shift_int ..).2]; simp_rw [likeref]; exact trade_integral hA hD he






end YM.SectorTools.PhysicalGaussianSwitch
