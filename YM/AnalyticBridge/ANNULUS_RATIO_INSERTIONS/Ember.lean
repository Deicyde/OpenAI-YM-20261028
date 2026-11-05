import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Arc

/-!
# E:r4 adapter to Gaussian ratio letters

Given envelope arithmetic (or a more general E score realization
input, for position orders).

Costs both endpoint and per label (the
numerical xγ=qweight square root).

Common marginal, possibly conditional
on frozen parameters.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Prism.Arc
open Function Filter ProbabilityTheory MeasureTheory Matrix Precision
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Schur
open scoped Topology BigOperators Classical ENNReal
variable {I : Type} [Fintype I] [DecidableEq I] {Ξ Ω : Type*} [MeasurableSpace Ω] {G : Gauge} {e : Ξ→I×I}

lemma roll (v u x : ℝ) (h : |v| ≤ x^2*u) (hx : 0≤x) (ht : x≤1) (hu : 0≤u) :
    |Real.exp v - 1| ≤ x*Real.exp (2*x*u) := by
  have he : |Real.exp v - 1| ≤ x^2*u*Real.exp (x^2*u) := by
    rcases lt_or_ge v 0 with hi|hi
    · rw [abs_of_nonpos (by linarith only [Real.exp_le_one_iff.mpr hi.le] : Real.exp v-1≤0)]
      rw [abs_of_neg hi] at h
      apply le_trans _ (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
      linarith only [h,Real.add_one_le_exp v]
    rw [abs_of_nonneg (by linarith only [Real.one_le_exp hi] : 0≤Real.exp v-1)]
    rw [abs_of_nonneg hi] at h
    have ht : Real.exp v*Real.exp (-v)=1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
    have hs := Real.add_one_le_exp (-v)
    calc
      _ ≤ v*Real.exp v := by nlinarith only [ht,mul_le_mul_of_nonneg_left hs (Real.exp_pos v).le]
      _ ≤ _ := mul_le_mul h (Real.exp_monotone h) (Real.exp_pos _).le (by positivity)
  apply he.trans
  rw [show 2*x*u=x*u+x*u by ring,Real.exp_add,show x^2*u=x*(x*u) by ring]
  apply le_trans (b:=x*Real.exp (x*u)*Real.exp (x*u)) _ (by rw [mul_assoc])
  gcongr
  · linarith only [Real.add_one_le_exp (x*u)]
  exact mul_le_of_le_one_left hu ht

/-- xγ convention, including any desired conditional dependence. -/
def coal (q : Ξ → Ω × Prices G I → ℝ) (i : Ξ) (z : Ω × Prices G I) : ℝ := Real.exp (q i z)-1
lemma readable (q : Ξ → Ω × Prices G I → ℝ) (i : Ξ) (h : Measurable (q i)) : Measurable (coal q i) := (Real.measurable_exp.comp h).sub measurable_const

lemma tariff {Y : Finset Ξ} {q : Ξ → Ω × Prices G I → ℝ} {x : Ξ → ℝ} {L : ℝ}
    (n : ℕ) (he : ∀ i∈Y, 0≤x i ∧ x i ≤ 1)
    (hh : ∀ j:I,hits e Y (fun i=>n*(2*x i)) j ≤ pinch L)
    (hf : ∀ i∈Y, Measurable (q i)) (hz : ∀ i∈Y, ∀ t,|q i t| ≤ x i^2*mast e i t.2) :
    Covered e Y (fun i=>x i^n) (fun i=>n*(2*x i)) (fun i t => (coal q i t)^n) L := by
  refine ⟨fun i hi=>pow_nonneg (he i hi).1 _,fun i hi=>by have h := (he i hi).1; positivity,
    hh,fun i hi=>(readable q i (hf _ hi)).pow_const _,?_⟩
  intro i hi y
  have hv : 0≤mast e i y.2 := zero_le_one.trans (mast_one e i y.2)
  have h := pow_le_pow_left₀ (abs_nonneg _) (roll _ _ _ (hz i hi y) (he i hi).1 (he i hi).2 hv) n
  simp only [coal,Real.norm_eq_abs,abs_pow]
  rw [mul_pow,← Real.exp_nat_mul,mul_assoc (2:ℝ),← mul_assoc _ (2:ℝ), ← mul_assoc _ _ (mast e i y.2),mul_assoc _ 2 (x i)] at h
  exact h

variable {L : ℝ}
/-- Equivalent to the  fourth norm test on this marginal,
uses same q even with triggers in Ω. `x` are absolute coefficient
square roots. L1 assertions for the fourth tester (no smoothness
beyond Borel). No rate subtraction on the empty label case (exact one). -/
lemma r4 (L : ℝ) (hl : 0<L) : ∃ M : ℝ, 1 ≤ M ∧
    ∀ {I : Type} [Fintype I] [DecidableEq I] {Ξ Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {C : Gaussian.Table (I × G.ColorIndex)} {η : ℝ}, C.PosSemidef → Numeric C η L →
    ∀ {Y : Finset Ξ} {e : Ξ → I × I} {q : Ξ → Ω × Prices G I → ℝ} {x : Ξ → ℝ},
      (∀ i∈Y, 0≤x i ∧ x i ≤ 1) → (∀ j:I,hits e Y (fun i=>4*(2*x i)) j ≤ pinch L) →
      (∀ i∈Y, Measurable (q i)) → (∀ i∈Y, ∀ t,|q i t| ≤ x i^2*mast e i t.2) →
      let U := μ.prod (cloud C)
      let v y := (∏ i∈Y, (coal q i y))^4
      Integrable v U ∧ (∫ y,v y ∂U) ≤ (∏ i∈Y,M*x i)^4 := by
  obtain ⟨D,hD,H⟩ := same_law (G:=G) L hl 0
  let a := Real.exp (pinch L)*tuck G^2
  have hA : 1≤a := one_le_mul_of_one_le_of_one_le (Real.one_le_exp (pinch_pos hl).le) (one_le_pow₀ (tuck_one _))
  refine ⟨D*a,one_le_mul_of_one_le_of_one_le hD hA,?_⟩
  intro I hI _ Ξ Ω hΩ μ hμ C η hC hx Y e q x he hh hf hz U f
  have H₀ : ∀ j:I,hits e Y (fun i=>(4:ℕ)*(2*x i)) j ≤ pinch L := hh
  obtain ⟨ht,hb⟩:= H μ hC hx ∅ ∅ (tariff 4 he H₀ hf hz) (show (0:ℝ) ≤ 0 from le_rfl) zero_le_one (fun _=>(1:ℝ)) measurable_const
    (fun _=>by simp [scores]) (fun _ _ _ hi => by simp at hi)
  have hs (y : Ω × Prices G I) : f y = 1*wires Y (fun i y => (coal q i y)^4) y := by
    unfold f wires; rw [one_mul,Finset.prod_pow] -- direction?
  have ht' (y: Ω × Prices G I) : ‖1*wires Y (fun i y => (coal q i y)^4) y‖ = f y := by
    rw [← hs,Real.norm_of_nonneg]; exact Even.pow_nonneg (by decide) _
  simp_rw [ht',Finset.card_empty,tail,dusk] at hb
  norm_num only [mul_zero,pow_zero,neg_zero,Real.exp_zero,one_pow,zero_mul,Nat.cast_zero,pow_one, one_mul,mul_one,add_zero] at hb
  have hi : Integrable f U := ht.congr (ae_of_all _ (fun i=>(hs i).symm))
  refine ⟨hi,?_⟩
  by_cases hY : Y.Nonempty
  swap
  · have hy : Y=∅ := Finset.not_nonempty_iff_eq_empty.mp hY
    change (∫ y, (∏ i∈Y, coal q i y)^4 ∂U) ≤ _
    have : IsProbabilityMeasure U := by unfold U; infer_instance
    simp [hy]
  apply hb.trans
  rw [← Finset.prod_pow]
  change D* (∏ i∈Y,a*x i^4) ≤ ∏ i∈Y,(D*a*x i)^4
  have hM : D ≤ ∏ i∈Y, D := by
    obtain ⟨i,hi⟩ := hY
    have he : 1 ≤ Y.card := Finset.card_pos.mpr ⟨i,hi⟩
    rw [Finset.prod_const]; nth_rw 1 [← pow_one D]; exact pow_le_pow_right₀ hD he
  refine le_trans (mul_le_mul_of_nonneg_right hM (Finset.prod_nonneg (fun i hi=>mul_nonneg (by linarith) (Even.pow_nonneg (by decide) _)))) ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i hi=>by have ha : 0 < a := lt_of_lt_of_le zero_lt_one hA; have ht : 0 < D := lt_of_lt_of_le zero_lt_one hD; positivity) (fun i _=>?_)
  rw [mul_pow,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (le_self_pow₀ (one_le_mul_of_one_le_of_one_le hD hA) (by norm_num)) (Even.pow_nonneg (by decide) _)
end YM.AnalyticBridge.AnnulusRatioInsertions.Prism.Arc
