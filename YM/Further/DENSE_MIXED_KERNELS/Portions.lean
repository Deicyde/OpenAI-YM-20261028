import YM.Further.DENSE_MIXED_KERNELS.Moments

/-!
# Shared fourth-budget and its evaluation

Useful for the protocol 'joint ratio factors have a fourth-moment
bound' and 'physical trigger events have a JOINT probability bound'.
Like a Hölder estimate but lets the polynomial price for the common
kernel enlarge to its second (still polynomial) price. Implements both
on the same marginal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module Port Gaussian Surface
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {X : Type*} {ρ : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype ρ]

/-- Positive, measurable (legitimate at every configuration) per-*occurrence*
bills, fourth moment of product (not deduced from fourth of each!). -/
structure Fourth (μ : Measure X) (f : ρ → X → ℝ) : Prop where
  nonneg i x : 0 ≤ f i x
  meas i : Measurable (f i)
  reads : Integrable (fun x => (∏ i,f i x)^4) μ
  holds : (∫ x, (∏ i,f i x)^4 ∂μ) ≤ 1

namespace Fourth
variable {f g : ρ → X → ℝ} {h : X → ℝ} {z : ℝ}
theorem charges (H : Fourth μ f) (L : Fourth μ g)
    (hh : Measurable h) (hw : ∀ x, 0≤h x) (he : Integrable (fun x => h x^2) μ)
    (hq : (∫ x,h x^2 ∂μ) ≤ z) :
    let a := fun x => (∏ i,f i x)*(∏ i,g i x)*h x
    Integrable a μ ∧ (∫ x,a x ∂μ) ≤ 2+z := by
  intro a
  let p x := ∏ i,f i x
  let q x := ∏ i,g i x
  have hp : Measurable p := Finset.measurable_fun_prod _ fun i _ => H.meas i
  have hq' : Measurable q := Finset.measurable_fun_prod _ fun i _ => L.meas i
  let b x := p x^4 + q x^4 + h x^2
  have hl x : 0 ≤ a x := mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => H.nonneg i x)
    (Finset.prod_nonneg fun i _ => L.nonneg i x)) (hw x)
  have hy x : a x ≤ b x := by
    change p x*q x*h x ≤ _; unfold b
    nlinarith only [sq_nonneg (p x*q x - h x), sq_nonneg (p x^2 - q x^2), sq_nonneg (h x),sq_nonneg (p x*q x)]
  have hB : Integrable b μ := (H.reads.add L.reads).add he
  have hA := hB.mono' (show AEStronglyMeasurable a μ from ((hp.mul hq').mul hh).aestronglyMeasurable) (Eventually.of_forall fun i => by
    rw [Real.norm_of_nonneg (hl i)]; exact hy i)
  refine ⟨hA,(integral_mono hA hB hy).trans ?_⟩
  unfold b at *
  have hi : Integrable (fun x => p x^4) μ := H.reads
  have hj : Integrable (fun x => q x^4) μ := L.reads
  rw [integral_add (g:=fun x => h x^2) (f:=fun x : X => p x^4+q x^4) (hi.add hj) he,integral_add hi hj]
  exact add_le_add (by linarith [show (∫ x,p x^4 ∂μ)≤1 from H.holds,show (∫ x,q x^4 ∂μ)≤1 from L.holds]) hq

-- no unbounded ratios/events needed for some sector terms



end Fourth

section Surface
variable {G : Gauge} {ι κ Ω : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Ω]
    {A : ChartRatio G} {H : Port A} {m : Measure Ω} {S : Surface H ι κ Ω} {w : ℝ}
    {f g : ρ → Ω × H.front ι (H.Room κ) → ℝ} {F P : ρ → Ω × H.back ι (H.Room κ) → ℝ}
local notation "I" => Ω × H.front ι (H.Room κ)
local notation "Y" => Ω × H.back ι (H.Room κ)



variable [IsProbabilityMeasure m]


lemma Fourth.allow (hF : Fourth (S.aboard m w) F) (hP : Fourth (S.aboard m w) P) (h : S.Valid) (hh : 0<w) {c : ℝ}
    (hc : 0<c) (he : ∀ i x,c*‖x‖^2 ≤ S.B i x x) (k : ℕ) :
    let f x := S.confirm w x*((∏ i,F i x)*(∏ i,P i x)*S.tower w x^k)
    Integrable f (ambient H ι κ m) ∧ (∫ x,f x ∂ambient H ι κ m) ≤ 2+due H ι κ (k*2) c := by
  obtain ⟨hb,hb'⟩ := h.returned (μ:=m) hh (k*2) hc he
  let g x := S.tower w x^k
  simp_rw [pow_mul] at hb hb'
  obtain ⟨hi,hi'⟩ := hF.charges hP (h:=g) (h.tower_meas.pow_const k)
    (fun x => by unfold g Surface.tower; positivity) hb hb'
  exact ⟨(h.charging hh).mp hi,(h.took hh hi).symm.trans_le hi'⟩
end Surface
end YM.Further.DenseMixedKernels
