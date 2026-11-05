import YM.TraceExtension.LogScaling

/- Explicit test-class receipts for Bochner expressions, in particular ordinary
 integrals at every positive scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}{S:Table C.book}{F:Spec.Final C X S}{μ:Measure E4}
lemma amp_compact {φ:E4→ℂ}(hp:Continuous φ)(he:HasCompactSupport φ)(h:TraceSpectrum F μ) (r:ℝ)(hr:0<r): Integrable (fun x:E4=> φ (r⁻¹ • x)) μ:= integrable_complex (allows_trace h) _ (hp.comp (by fun_prop : Continuous (fun x:E4=>r⁻¹ • x))) (HasCompactSupport.comp_smul he (inv_ne_zero hr.ne'))
lemma amp_s (φ:Probe E4)(h:TraceSpectrum F μ)(r:ℝ)(hr:0<r): Integrable (fun x:E4=> φ (r⁻¹ • x)) μ:=by
   haveI:= h.upper; exact (Probe.along (ContinuousLinearEquiv.smulLeft (Units.mk0 r⁻¹ (inv_ne_zero hr.ne'))) φ).integrable
lemma cone_int (φ:E4→ℂ) (hp:Integrable φ (coneMeasure (1536*Real.pi))): IntegrableOn (fun p=>m p^2 • φ p) cone volume:=by
   let M(x:E4):ℝ≥0:=⟨m x^2,sq_nonneg _⟩; have h:Measurable M:= Measurable.subtype_mk (show Measurable (fun x=>m x^2) from by fun_prop)
   have he(p:E4):ENNReal.ofReal ((1536*Real.pi)/(1536*Real.pi)* m p^2)=(M p:ℝ≥0∞):=by rw [div_self (by positivity),one_mul]; exact (@ENNReal.ofReal_coe_nnreal (M p))
   change Integrable _ ((volume.restrict _).withDensity _) at hp
   simp_rw[he] at hp
   exact (integrable_withDensity_iff_integrable_smul h).1 hp
lemma cone_int_s(φ:Probe E4): IntegrableOn (fun p=>m p^2 • φ p) cone volume:=by
   haveI:= cone_temperate (A:=1536 * Real.pi) (by positivity)
   exact cone_int φ φ.integrable
lemma cone_int_c {φ:E4→ℂ}(hp:Continuous φ)(he:HasCompactSupport φ): IntegrableOn (fun p=>m p^2 • φ p) cone volume:= cone_int φ (integrable_complex (allows_cone _ (by positivity)) _ hp he)
end YM.TraceExtension
