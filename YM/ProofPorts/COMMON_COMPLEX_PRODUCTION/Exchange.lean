import YM.Next.SCHEDULE.Postal
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.BlockLaw
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Pin

/-! # Pin exchange and return to the ORIGINAL common Gaussian. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction.Pin
open Set Function Filter Matrix Lattice RG Wilson Precision Multi.Vacuum Next.SectorChange
open MeasureTheory Gaussian Gauss
open scoped Topology BigOperators Classical MatrixOrder
variable {G : Gauge} {I : Type} [Fintype I] [DecidableEq I] (P : Pin G I)

private abbrev Split := Prices G P.Floats × P.Shift
private def percentage (m z : P.Shift) : ℝ := if P.zone m z ∈ mouth P.chart then pay P.chart (P.zone m z) else 0

private lemma percentage_pos {P : Pin G I} (h : P.Clean) (m z : P.Shift) : 0 ≤ P.percentage m z := by
  unfold percentage; split; next he => exact (h.chart_pos he).le
  rfl

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]

private def pct (m : P.Shift) (v : P.Group) (f : P.State → X) (z : P.Split) :=
    percentage P m z.2 • f (z.1,release v (P.zone m z.2))

def returnWeight (C : Gaussian.Table (I × G.ColorIndex)) (m : P.Shift) (v : P.Group) (f : P.State → X) (z : Prices G I) :=
    let y := CFC.sqrt C *ᵥ z
    P.faceFee C m y • f (P.fetch m v y)

namespace Clean
variable {P} (h : P.Clean) (m : P.Shift) (v : P.Group) (C : Gaussian.Table (I × G.ColorIndex)) (hc : C.PosDef)
include h

private lemma part (f : P.State → X) (hm : Measurable f) (he : ∀ x, x∉P.scan v → f x=0) (z : Prices G P.Floats) :
    let k := P.pct m v f
    let μ := piHaar G P.Stays
    (Integrable (fun y => f (z,y)) μ ↔ Integrable (fun y => k (z,y))) ∧
      (∫ y,f (z,y) ∂μ) = P.g ^ Fintype.card (P.Stays × G.ColorIndex) • ∫ y,k (z,y) := by
  intro k μ
  obtain ⟨ht,hI⟩ := release_integral h.legal v (fun y => f (z,y)) (hm.comp measurable_prodMk_left).stronglyMeasurable
    (fun y => he (z,y))
  let F : LogArray G P.Stays→X := (mouth P.chart).indicator fun y => pay P.chart y • f (z, release v y)
  obtain ⟨h1,h2⟩ := Gaussian.paid_scale h.pos (F ∘ tape) m
  rw [(tape_volume (G:=G)).integrable_comp_emb tape.measurableEmbedding (g:=F)] at h1
  change (∫ y,F (tape y))=_ at h2
  rw [(tape_volume (G:=G)).integral_comp' F] at h2
  have hf y : (F ∘ tape) (m + P.g • y) = k (z,y) := by
    change F (P.zone m y)=ite _ _ (0:ℝ) • _
    unfold F Set.indicator; split <;> simp_all
  exact ⟨ht.trans (by simp_rw [hf] at h1; exact h1),hI.trans (by simp_rw [hf] at h2; exact h2)⟩

private lemma pct_meas (f : P.State → X) (hm : Measurable f) : Measurable (P.pct m v f) := by
  have ht : Measurable (fun p:P.Split => P.zone m p.2) := (P.zone_meas m).comp (measurable_snd (α:=Prices G P.Floats) (β:=P.Shift))
  have he : Measurable (fun y : P.Split => P.percentage m y.2) := (Measurable.ite (ht (mouth_meas _)) ((pay_meas h.legal).comp ht) (measurable_const (a:=(0:ℝ))))
  exact he.smul (hm.comp (measurable_fst.prodMk ((release_continuous _).measurable.comp ht)))

private lemma slice_price (f : P.State → X) (hm : Measurable f) (he : ∀ x, x∉P.scan v → f x=0) :
    let k := P.pct m v f
    (Integrable f P.basis ↔ Integrable k) ∧
    (∫ y,f y ∂P.basis) = P.g ^ Fintype.card (P.Stays × G.ColorIndex) • ∫ y,k y := by
  intro k; let s := P.g ^ Fintype.card (P.Stays × G.ColorIndex)
  have hs : s ≠ 0 := pow_ne_zero _ h.pos.ne'
  haveI : SFinite (piHaar G P.Stays) := by unfold piHaar; infer_instance
  have hm' := h.pct_meas m v _ hm
  have hi : Integrable f P.basis ↔ Integrable k := by
    rw [basis,Measure.volume_eq_prod (Prices G P.Floats) P.Shift,integrable_prod_iff hm'.aestronglyMeasurable,
      integrable_prod_iff hm.aestronglyMeasurable]
    simp_rw [(h.part m v _ hm he _).1,(h.part m v (fun x => ‖f x‖) hm.norm (fun x hx => by rw [he _ hx,norm_zero]) _).2]
    have hk y : pct P m v (fun x => ‖f x‖) y = ‖k y‖ := (norm_smul_of_nonneg (percentage_pos h ..) _).symm
    simp_rw [hk]
    exact and_congr_right' (integrable_smul_iff (μ:=volume) hs (fun x => ∫ y, ‖k (x,y)‖))
  refine ⟨hi,?_⟩
  by_cases hf : Integrable f P.basis
  · unfold basis; rw [Measure.volume_eq_prod (Prices G P.Floats) P.Shift,integral_prod _ (hi.mp hf),integral_prod f hf]
    simp_rw [(h.part m v _ hm he _).2,integral_smul]; rfl
  rw [integral_undef hf,integral_undef (mt hi.mpr hf),smul_zero]

include hc
private lemma exchange_form (f : P.State → X) (hm : Measurable f) (he : ∀ x, x∉P.scan v → f x=0) :
    let k y := Real.exp (force C y/2) • P.pct m v f (P.switch y)
    let d := P.g ^ Fintype.card (P.Stays × G.ColorIndex) * Gaussian.coat C
    (Integrable f P.basis ↔ Integrable k (cloud C)) ∧ (∫ y,f y ∂P.basis)= d • ∫ z,k z ∂cloud C := by
  have hu:=h.slice_price m v f hm he
  have he' := under_cloud hc (P.pct m v f ∘ P.switch)
  refine ⟨(hu.1.trans (P.units.integrable_comp_emb P.switch.measurableEmbedding).symm).trans he'.1,?_⟩
  rw [hu.2,← P.units.integral_comp' (P.pct m v f),mul_smul]; exact congrArg _ he'.2

/-- The total integral (Bochner), in either direction, at a given θ,U. Needs
vanishing off the held chart in State; use for EACH derivative in unforced
price. No conditioning or deleting coordinates during derivative estimates. -/
theorem exchange (f : P.State → X) (hm : Measurable f) (he : ∀ x, x∉P.scan v → f x=0) :
    (Integrable f P.basis ↔ Integrable (P.returnWeight C m v f) (standard _)) ∧
      (∫ y,f y ∂P.basis)=∫ z,P.returnWeight C m v f z ∂standard _ := by
  let k y := Real.exp (force C y/2) • P.pct m v f (P.switch y)
  let d := P.g ^ Fintype.card (P.Stays × G.ColorIndex) * Gaussian.coat C
  have hd : d≠0 := mul_ne_zero (pow_ne_zero _ h.pos.ne') (coat_pos hc).ne'
  have hm' : Measurable k := by
    have hq : Measurable (fun y => Real.exp (force C y / 2)) := by unfold force mulVec dotProduct; fun_prop
    exact hq.smul ((h.pct_meas m v f hm).comp P.switch.measurable)
  let w (y : Prices G I) := CFC.sqrt C *ᵥ y
  have hw : P.returnWeight C m v f=d • (k ∘ w) := by
    funext z; unfold returnWeight faceFee; dsimp only; split
    next hi =>
      change _ = d • (Real.exp _ • ((ite (P.zone m (P.switch (w z)).2 ∈ mouth P.chart) _ (0:ℝ)) • (_ : X)))
      rw [if_pos (show P.zone m (P.switch (w z)).2 ∈ mouth P.chart from hi),smul_smul,smul_smul]
      congr 1
      unfold d w; ring
    next hi => simp [smul_zero,zero_smul,d,w,k,pct,percentage, show P.zone m (P.switch (w z)).2 ∉ mouth P.chart from hi]
  have hx := h.exchange_form m v C hc f hm he
  have ht : Measure.map w (standard _) = cloud C := paid C
  rw [hw,integrable_smul_iff hd,←integrable_map_measure hm'.aestronglyMeasurable (measurable_matVec _).aemeasurable,ht]
  refine ⟨hx.1,hx.2.trans ?_⟩
  change _ = ∫ z,d • k (w z) ∂standard _
  rw [integral_smul,← integral_map (measurable_matVec _).aemeasurable hm'.aestronglyMeasurable,ht]

lemma ret_pinned (f : Prices G I → ℂ) (he : ∀ y, y∉P.trace m → f y=0) (z : Prices G I) :
    P.returnWeight C m v (P.pinned C m v f) z = f (CFC.sqrt C *ᵥ z) := by
  unfold returnWeight pinned; dsimp only
  by_cases hz : (CFC.sqrt C *ᵥ z) ∈ P.trace m
  · rw [Set.indicator_of_mem (seen_inside v hz) _,smul_smul,h.reimbursed hc v hz,h.unwinds v hz,one_smul]
  rw [faceFee,if_neg hz,zero_smul,he _ hz]

lemma pinned_price (f : Prices G I → ℂ) (hm : Measurable (P.pinned C m v f)) (he : ∀ y, y∉P.trace m → f y=0) :
    (Integrable (P.pinned C m v f) P.basis ↔ Integrable (fun z => f (CFC.sqrt C *ᵥ z)) (standard _)) ∧
      (∫ z,P.pinned C m v f z ∂P.basis) = ∫ z,f (CFC.sqrt C *ᵥ z) ∂standard _ := by
  rw [← funext (h.ret_pinned m v C hc f he)]
  exact h.exchange m v C hc _ hm (fun x hx => Set.indicator_of_notMem hx _)
end Clean
end YM.ProofPorts.CommonComplexProduction.Pin
