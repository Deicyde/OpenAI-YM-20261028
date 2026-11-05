import YM.TraceExtension.Fock.Tests
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {G:Gauge}{C:Family G}{a: Extraction.Order}{S:Table C.book}{F: Spec.Final C a S}{m:ℕ}{U:F.action.operators.H→ₗᵢ[ℂ] Ambient m}(X: Comparison F U){b:ℝ}(hp:EuclideanAsymptotic F b)(hb:0<b)
-- even just an average.Test. Image must be invariant. Can take weak/scalar integrals only, no assumptions on separability needed.
variable {I:Type*}[MeasurableSpace I](μ:Measure I)[IsProbabilityMeasure μ]
include μ X hp hb
-- weaker than isometries on ambient: scalar tensors defined on wave amplitudes in ambient
lemma smell (P:I → Ambient m→ Ambient m) (Y:∀ i x y, PhysicalWave x→ PhysicalWave y→ inner ℂ (P i x) (P i y)=inner ℂ x y) (p:∀ i x,P i (U x)=U x)(r:ℝ)(hr:0 <r):
    ¬ (∀ (Q W:Set E4), IsOpen Q→IsOpen W→closure Q⊆ball 0 r→(∀ x∈closure Q,∀ y∈closure W,x-y∈spacelike)→
        ∀ (v:Test4)(h:TestList m), tsupport v⊆ Q → HasCompactSupport ⇑v→(∀ i,tsupport (h i)⊆W)→(∀ i,HasCompactSupport ⇑(h i))→(∀ i,Probe.bar (h i)=h i)→
          (∫ z,inner ℂ (P z (coherent (-h))) (signal F U v)∂μ)= (∫ z,inner ℂ (signal F U (Probe.bar v)) (P z (coherent h))∂μ)) :=by
    intro ht; apply regions_excludes hr hb hp X; refine ⟨ContinuousLinearMap.id ℂ _, ?_,fun _=>rfl,?_⟩
    · exact ContinuousLinearMap.adjoint_id
    intro Q W hQ hW he hA v h hF ht' hx hv hw
    have hg(i)(x)(g:TestList m): inner ℂ (P i (coherent g)) (U x)=inner ℂ (coherent g) (U x):=by conv_lhs => rw[← p i x]; exact Y _ _ _ (coherent_iswave g) (X.ambient x)
    have hz(i)(x)(g:TestList m): inner ℂ (U x) (P i (coherent g))=inner ℂ (U x) (coherent g):=by rw[← inner_conj_symm,hg,inner_conj_symm]
    have hB:= ht Q W hQ hW he hA v h hF ht' hx hv hw; unfold signal at hB; simp_rw[hg,hz] at hB; simpa only[integral_const,probReal_univ,one_smul,ContinuousLinearMap.id_apply,signal] using hB
end YM.TraceExtension.Photons
