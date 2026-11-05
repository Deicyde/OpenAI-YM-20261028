import YM.Further.DENSE_MIXED_KERNELS.Arc

/-! Hard output analogue, no differentiability or regular point
assumed. Still on the COMMON marginal/occurrence integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module Port Gaussian Surface
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {U : Config G n} {M t : ℝ} {k : ℕ}
variable {ι κ Ω α : Type} [Fintype ι] [Fintype κ] [Fintype α] [MeasurableSpace Ω]
    {A : ChartRatio G} {H : Port A} {μ : Measure Ω} {W : Config G n→Surface H ι κ Ω}
    {P : Directions G n → Prop} {c C g : ℝ}
local notation "X" => H.front ι (H.Room κ)
local notation "Y" => Ω × H.back ι (H.Room κ)
variable {f : α → Config G n → Ω × H.back ι (H.Room κ) → ℂ} {b : α→ℝ}

/-- `U` the **coarse** configuration. -/
structure Dark (W : Config G n→Surface H ι κ Ω) (μ : Measure Ω) (f : α → Config G n → Ω × H.back ι (H.Room κ) → ℂ) (U : Config G n)
    (b : α→ℝ) (g : ℝ) : Prop where
  registered : (W U).Valid
  maps i : Measurable (f i U)
  finance : ∃ R L : α → Ω × H.back ι (H.Room κ)→ℝ, Fourth ((W U).aboard μ g) R ∧ Fourth ((W U).aboard μ g) L ∧
      ∀ i p, p ∈ (W U).Perch → ‖f i U p‖ ≤ b i*R i p*L i p

theorem Dark.evaluate (h : Dark W μ f U b g) [IsProbabilityMeasure μ] (hg : 0<g) (hb : ∀ i,0≤b i)
    (z : Y → ℂ) (he : Measurable z) (hm : 0≤M) (hM : ∀ y, ‖z y‖≤M) :
    let a := fun x => z x*whole W f g x U
    Integrable a (ambient H ι κ μ) ∧ ‖∫ y,a y ∂ambient H ι κ μ‖ ≤ M*(∏ i,b i)*3 := by
  intro a
  let ν := (W U).aboard μ g
  have hV := h.registered
  obtain ⟨R,L,hR,hL,hl⟩ := h.finance
  have hn : IsFiniteMeasure ν := hV.landed g hg μ
  let Q := (W U).confirm g
  let D x := Q x *((∏ i,R i x) * (∏ i,L i x)*1)
  let m := M*(∏ i,b i)
  have hm' : 0≤m := mul_nonneg hm (Finset.prod_nonneg fun i _ => hb i)
  obtain ⟨hi,hi'⟩ := hR.charges hL (h:=fun _ => 1) (z:=1) measurable_const (fun _ => zero_le_one) (by
    change Integrable _ ν; simp) (by
    change (∫ _,(1:ℝ)^2 ∂ν) ≤ 1
    have hv := ENNReal.toReal_mono (b:=1) (by simp) (hV.sub_one g hg μ); change (ν Set.univ).toReal≤_ at hv
    simp_all [measureReal_def])
  have ht : Integrable D (ambient H ι κ μ) := (hV.charging hg).mp hi
  have hcov : (∫ y,D y ∂ambient H ι κ μ) ≤ 3 := by linarith [(show (∫ y,D y ∂ambient H ι κ μ) ≤ 2+1 from (hV.took hg hi).symm.trans_le hi')]
  have he' x : ‖a x‖ ≤ m*D x := by
    unfold a m D whole; rw [norm_mul,norm_smul,Real.norm_of_nonneg (hV.confirm_nonneg _ hg _), norm_prod]
    by_cases hp : x∈(W U).Perch
    · let e i := b i * R i x * L i x
      have hv : ∏ i, ‖f i U x‖ ≤ ∏ i,e i := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hl i x hp)
      refine (mul_le_mul (hM x) (mul_le_mul_of_nonneg_left hv (hV.confirm_positive g hg x hp).le) ?_ hm).trans_eq ?_
      · exact mul_nonneg (hV.confirm_nonneg g hg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      unfold Q e; rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]; ring
    · change ‖z x‖*(Q x*_ ) ≤ _* (Q x* _)
      have hv : Q x=0 := if_neg hp
      rw [hv,zero_mul,zero_mul,mul_zero,mul_zero]
  have hh : Integrable a (ambient H ι κ μ) := (ht.const_mul _).mono'
    (he.mul ((hV.confirm_meas _).smul (Finset.measurable_fun_prod _ fun i _ => h.maps i))).aestronglyMeasurable (Eventually.of_forall he')
  refine ⟨hh,(norm_integral_le_integral_norm _).trans ?_⟩
  apply (integral_mono hh.norm (ht.const_mul _) he').trans
  rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hcov hm'

end YM.Further.DenseMixedKernels
