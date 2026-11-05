import YM.Trace.BoundaryUnique
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Parameter integration over a compact support (strict contour interior). -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.Trace
open Function MeasureTheory Complex Set Filter
open scoped Interval Topology ContDiff ENNReal BigOperators

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [CompactSpace X]
    {F : ℂ → X → ℂ} {s : Set ℂ}

lemma contour_continuous (H : ContinuousOn (uncurry F) (s ×ˢ univ)) (hs : IsOpen s) :
    ContinuousOn (fun z => ∫ x,F z x ∂μ) s := by
  apply hs.continuousOn_iff.mpr; intro z hz
  obtain ⟨r,hr,hR⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz)
  let U := Metric.closedBall z r ×ˢ (univ : Set X)
  obtain ⟨C,hC⟩ := (isCompact_closedBall z r|>.prod CompactSpace.isCompact_univ).bddAbove_image (f:=fun p : ℂ × X => ‖F p.1 p.2‖)
    (H.norm.mono (prod_mono hR Subset.rfl))
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    ?_ ?_ (integrable_const _) (.of_forall fun x => ?_)
  · filter_upwards [Metric.closedBall_mem_nhds z hr] with p hp
    have hh : Continuous (F p) := continuous_iff_continuousAt.mpr (fun x=> by
       change ContinuousAt (uncurry F ∘ (fun y => (p,y))) _
       apply ((((hs.prod isOpen_univ).continuousOn_iff.mp H) (by exact ⟨hR hp, mem_univ _⟩)).comp
         (by fun_prop)))
    exact hh.aestronglyMeasurable
  · filter_upwards [Metric.closedBall_mem_nhds z hr] with p hp
    exact .of_forall fun x => hC (mem_image_of_mem _ ((prodMk_mem_set_prod_eq ..).mpr ⟨hp,mem_univ _⟩))
  apply ((hs.prod isOpen_univ).continuousOn_iff.mp H _) |>.tendsto.comp
    (tendsto_id.prodMk_nhds tendsto_const_nhds)
  exact ⟨hz,mem_univ _⟩

lemma line_swap (H : ContinuousOn (uncurry F) (s ×ˢ univ)) {a b : ℝ} {l : ℝ→ℂ} (hc : Continuous l)
    (hl : MapsTo l (uIcc a b) s) :
    Integrable (fun x => ∫ y in a..b, F (l y) x) μ ∧
    (∫ y in a..b, ∫ x, F (l y) x ∂μ)= (∫ x, (∫ y in a..b, F (l y) x) ∂μ) := by
  suffices ∀ w⊆ uIcc a b, MeasurableSet w →
      Integrable (uncurry (fun y=> F (l y))) (((volume : Measure ℝ).restrict w).prod μ) by
    have ha := this (Ioc a b) (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_uIcc) measurableSet_Ioc
    have hb := this (Ioc b a) (Ioc_subset_Icc_self.trans (uIcc_comm b a ▸ Icc_subset_uIcc)) measurableSet_Ioc
    unfold intervalIntegral
    constructor
    · exact ha.integral_prod_right.sub hb.integral_prod_right
    erw [integral_integral_swap ha,integral_integral_swap hb, integral_sub ha.integral_prod_right hb.integral_prod_right]
    rfl
  intro w hw _
  have hi : ContinuousOn (uncurry fun y=> F (l y)) (uIcc a b ×ˢ (univ : Set X)) := by
    exact H.comp (f:=(fun p : ℝ×X => (l p.1, p.2))) (by fun_prop) (fun p hp => ⟨hl hp.1,hp.2⟩)
  rw [← show μ.restrict univ=μ from Measure.restrict_univ, Measure.prod_restrict]
  exact ((ContinuousOn.integrableOn_compact (isCompact_uIcc.prod CompactSpace.isCompact_univ) hi).mono_set (prod_mono hw Subset.rfl))

lemma contour_analytic_compact (hs : IsOpen s) (H : ContinuousOn (uncurry F) (s ×ˢ univ))
    (h : ∀ x, DifferentiableOn ℂ (F · x) s) : DifferentiableOn ℂ (fun z => ∫ x,F z x ∂μ) s := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hs).mp
  refine ⟨fun z w hw => ?_, contour_continuous H hs⟩
  suffices HH : ∀ {z w:ℂ}, Rectangle z w ⊆ s → wedgeIntegral z w (fun z' => ∫ x,F z' x ∂μ) = ∫ x, wedgeIntegral z w (fun z' => F z' x) ∂μ by
    rw [HH hw, HH (z:=w) (w:=z) (by simpa only [Rectangle,uIcc_comm w.re,uIcc_comm w.im])]
    rw [← MeasureTheory.integral_neg]
    exact integral_congr_ae (.of_forall fun x => (h x).isConservativeOn z w hw)
  intro z w hw
  let l (x : ℝ) := (x : ℂ)+z.im*I; let l' (x : ℝ) := (w.re : ℂ)+x*I
  have h1 := line_swap (μ:=μ) H (l:=l) (by fun_prop) (a:=z.re) (b:=w.re)
    (fun x hx => hw (by simpa [l,Rectangle,mem_reProdIm] using! hx))
  have h2 := line_swap (μ:=μ) H (l:=l') (by fun_prop) (a:=z.im) (b:=w.im)
    (fun x hx => hw (by simpa [l',Rectangle,mem_reProdIm] using! hx))
  erw [wedgeIntegral,h1.2,h2.2,← MeasureTheory.integral_smul]
  symm; exact integral_add h1.1 (h2.1.const_mul _)

lemma contour_analytic {Z : Type*} [TopologicalSpace Z] [T2Space Z] [MeasurableSpace Z]
    [BorelSpace Z] {μ : Measure Z} [IsFiniteMeasureOnCompacts μ] {F : ℂ→Z→ℂ} (hs : IsOpen s) {u : Set Z} (hu : IsCompact u)
    (H : ∀ z ∈ s, ∀ x ∉ u, F z x = 0) (he : ContinuousOn (uncurry F) (s ×ˢ (univ : Set Z))) (ht : ∀x, DifferentiableOn ℂ (F · x) s) :
    DifferentiableOn ℂ (fun z=> ∫ x,F z x∂μ) s := by
  let ν : Measure (u) := μ.comap Subtype.val
  haveI : @CompactSpace u _ := isCompact_iff_compactSpace.mp hu
  haveI : BorelSpace u := inferInstance
  haveI : IsFiniteMeasure ν := ⟨show Measure.comap ((↑):u → Z) μ univ < ⊤ from (by
     simpa [(MeasurableEmbedding.subtype_coe hu.measurableSet).comap_apply] using hu.measure_lt_top (μ:=μ))⟩
  let y (z : ℂ) := ∫ x:u,F z x∂ν
  have hd : DifferentiableOn ℂ y s := contour_analytic_compact (μ:=ν) (F:=fun z x => F z x) hs
    (he.comp (f:=Prod.map id ((↑):u→Z)) (by fun_prop) (fun p hp => ⟨hp.1, mem_univ _⟩)) (fun i=> ht i)
  exact hd.congr (fun z hz => (integral_subtype_comap hu.measurableSet _ |>.trans (setIntegral_eq_integral_of_forall_compl_eq_zero (H _ hz))).symm)
end YM.Trace
