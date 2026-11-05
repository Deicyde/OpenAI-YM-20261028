import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Jets
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Trades
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment
import YM.Planned.STATIONARY_JET_PORT.AtHome
/-!
# Warping FULL base dice with clock.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented   Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Shield AbsoluteSums
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace F] {μ : Measure F}
variable {ι : Type} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ) (hQ : Q.PosDef) {a : ℝ} (ha : 0<a)
local notation "X" => Poll.Body ι
local notation "A" => Poll.sweep Q

def walk (a : ℝ) (x:X) := a^Fintype.card ι * (lens₀ Q (a • x)/lens₀ Q x)

lemma bristle (a:ℝ) (ha:0<a) (x:X) : 0< walk Q a x:= mul_pos (pow_pos ha _) (div_pos (fullFuel ..) (fullFuel ..))
lemma rated (a:ℝ) : Measurable (walk Q a):= by
  have hx : Measurable (lens₀ Q) := Shield.bulbB (z:=id) (S:=fun _ : X=>Q) (fun _ _=>measurable_const) measurable_id
  exact measurable_const.mul ((hx.comp (show Measurable (fun x:X=>a • x) from continuous_id.const_smul a|>.measurable)).div hx)
lemma mapped {E : Type*} [MeasurableSpace E] (μ : Measure E) {Xt : E→ℝ≥0∞} (e : E≃ᵐ E) : (μ.withDensity (Xt ∘ e)).map e=(μ.map e).withDensity Xt:= by
  ext i hi; rw [Measure.map_apply e.measurable hi, withDensity_apply _ hi, withDensity_apply _ (e.measurable hi),e.measurableEmbedding.restrict_map]; exact (e.measurableEmbedding.lintegral_map Xt).symm
-- joint measure witness.Ac.R odds
include ha hQ
lemma slope_inv : ∃ e : X ≃ᵐ X,(∀ x,e x=a • x) ∧ MeasurePreserving e ((A).withDensity (fun x=> ENNReal.ofReal (walk Q a x))) A := by
  let e: X≃ᵐ X:= (Homeomorph.smul (isUnit_iff_ne_zero.2 ha.ne').unit).toMeasurableEquiv
  let w:= walk Q a; let f(x:X):= ENNReal.ofReal (lens₀ Q x); let g x:= ENNReal.ofReal (w x)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp (Shield.bulbB (z:=id) (S:=fun _ : X=>Q) (fun _ _=>measurable_const) measurable_id); have hg: Measurable g:=ENNReal.measurable_ofReal.comp (rated Q a)
  refine ⟨e,fun x=> rfl,e.measurable,?_⟩; rw [magnifies Q hQ]; let q:=a^Fintype.card ι; have hq : 0 < q:= pow_pos ha _
  let μ:=volume (α:=X); change Measure.map e ((μ.withDensity f).withDensity g)=μ.withDensity f
  have ht : f*g= ENNReal.ofReal q • (f ∘ e):= funext fun i=>by
    change ENNReal.ofReal _ * ENNReal.ofReal (q*(_/_))=ENNReal.ofReal q*ENNReal.ofReal (lens₀ Q (a • i))
    rw [← ENNReal.ofReal_mul (show 0 ≤ lens₀ Q i from (fullFuel ..).le), ← ENNReal.ofReal_mul hq.le]; congr 1; have hr:= fullFuel Q i; field_simp
  rw [← withDensity_mul μ hf hg,ht, withDensity_smul _ (hf.comp e.measurable), Measure.map_smul]
  rw [mapped,show μ.map e=ENNReal.ofReal (q⁻¹) • μ from ?_,withDensity_smul_measure,smul_smul,← ENNReal.ofReal_mul hq.le,mul_inv_cancel₀ hq.ne',ENNReal.ofReal_one,one_smul]
  convert! Measure.map_addHaar_smul μ ha.ne' using 1; rw [finrank_euclideanSpace]; unfold q; rw [abs_of_pos (by positivity : 0 < (a ^ Fintype.card ι)⁻¹)]
lemma earningsK [SFinite μ] (f : F × X → E) :
    (∫ x,f x ∂μ.prod A)=(∫ x,(walk Q a x.2) • f (x.1,a • x.2) ∂μ.prod A) ∧
     (Integrable f (μ.prod A)↔ Integrable (fun x=> (walk Q a x.2) • f (x.1,a • x.2)) (μ.prod A)):= by
  obtain ⟨e,he,h⟩:= slope_inv Q hQ ha; let e':= MeasurableEquiv.prodCongr (MeasurableEquiv.refl F) e
  let f' x:= ENNReal.ofReal (walk Q a x)
  have hx : Measurable f':=ENNReal.measurable_ofReal.comp (rated Q a); have hp : IsFiniteMeasure ((Poll.sweep Q).withDensity f'):= (Measure.isFiniteMeasure_map_iff (μ:=(A).withDensity f') (e.measurable.aemeasurable)).mp (by unfold f'; rw [h.map_eq]; infer_instance)
  have H: MeasurePreserving e' ((μ.prod A).withDensity (f' ∘ Prod.snd)) (μ.prod A):= by
    change MeasurePreserving e' ((μ.prod (A)).withDensity (fun x=> f' x.2)) (μ.prod (A)); rw [← prod_withDensity_right hx]; exact (MeasurePreserving.id μ).prod h
  have hz t : (f' t).toReal=walk Q a t:= ENNReal.toReal_ofReal (bristle Q _ ha _).le
  have hP: (fun x=> ENNReal.toReal ((f' ∘ Prod.snd) x) • (f ∘ e') x)=(fun x=> walk Q a x.2 • f (x.1,a • x.2)):= by funext x; simp_rw [Function.comp_apply, hz,show e' x=(x.1,a • x.2) from (Prod.ext rfl (he ..))]
  constructor
  · rw [← H.integral_comp e'.measurableEmbedding,integral_withDensity_eq_integral_toReal_smul (hx.comp measurable_snd) (ae_of_all _ (fun x=> ENNReal.ofReal_lt_top))]; exact congr_arg (fun u => ∫ x,u x ∂μ.prod A) hP
  rw [← H.integrable_comp_emb e'.measurableEmbedding,integrable_withDensity_iff_integrable_smul' (hx.comp measurable_snd) (ae_of_all _ (fun x=> ENNReal.ofReal_lt_top))]; rw [hP]
end YM.PhysicalNext.Repeat.Alabaster
