import YM.TraceExtension.Fock.Conclude

/-! Optional weaker spacelike placement and averaging versions. No net
 is constructed or assumed to exist. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {G : Gauge} {C : Family G} {a : Extraction.Order} {S : Table C.book}
    {F : Spec.Final C a S} {m n : ℕ} {U : F.action.operators.H →ₗᵢ[ℂ] Ambient m} {A r: ℝ}

structure Regions (r:ℝ)(F:Spec.Final C a S)(U : F.action.operators.H →ₗᵢ[ℂ] Ambient m) : Prop where
    average_test : ∃ P: Ambient m →L[ℂ] Ambient m,P.adjoint=P ∧ (∀ x, P (U x)=U x) ∧ ∀ (Q W:Set E4), IsOpen Q→ IsOpen W → closure Q⊆ball 0 r →
        (∀ x∈closure Q,∀ y∈closure W,x-y∈spacelike) →
        ∀ (f:Test4) (h:TestList m), tsupport f ⊆ Q→HasCompactSupport ⇑f → (∀ i,tsupport (h i) ⊆ W) → (∀ i,HasCompactSupport ⇑(h i))→(∀ i,Probe.bar (h i)= h i)→
          inner ℂ (P (coherent (-h))) (signal F U f)=inner ℂ (signal F U (Probe.bar f)) (P (coherent h))

lemma Regions.localball (he:Regions r F U)(hr:0<r) : LocalTest F U := by
    obtain ⟨P,hP,hW,h⟩:= he.average_test
    refine ⟨r,hr,?_⟩; intro f hf hb g hg hR hh
    let X:= tsupport f; let Y:=⋃ i, tsupport (g i)
    have hx : IsCompact X:= hf
    have hy : IsCompact Y:=isCompact_iUnion hg
    let W := {p:E4×E4 | p.1-p.2∈spacelike}; have he : IsOpen W:= open_spacelike.preimage (continuous_fst.sub continuous_snd)
    obtain ⟨s,t,hs,ht,hS,hT,hw⟩:=generalized_tube_lemma hx hy he (by
       rintro ⟨x,y⟩ ⟨hv,hv'⟩; rcases mem_iUnion.mp hv' with ⟨i,hi⟩; exact hh i x hv y hi)
    obtain ⟨Q,hQ,hxQ,hC⟩:= hx.exists_isOpen_closure_subset (U:=s∩ball 0 r)
        (inter_mem (hs.mem_nhdsSet.mpr hS) (isOpen_ball.mem_nhdsSet.mpr hb))
    obtain ⟨L,hL,hYL,hE⟩:= hy.exists_isOpen_closure_subset (U:=t) (ht.mem_nhdsSet.mpr hT)
    have hv:=h Q L hQ hL (fun x hx=> (hC hx).2) (fun x hx y hy=> hw (show (x,y)∈s×ˢt from ⟨(hC hx).1,hE hy⟩)) f g hxQ hf (fun i x hx=> hYL (mem_iUnion.mpr ⟨i,hx⟩)) hg hR
    unfold signal at *
    conv at hv => lhs; rw [← ContinuousLinearMap.adjoint_inner_right,hP,hW]
    conv at hv => rhs; rw [← ContinuousLinearMap.adjoint_inner_left,hP,hW]
    exact hv
lemma regions_excludes (hr:0<r) (ha:0<A)(ht: EuclideanAsymptotic F A)(X:Comparison F U) : ¬ Regions r F U := by
    intro hi; obtain ⟨μ,hμ,-⟩:= traceSpectrum_exists F
    exact saturate X (hi.localball hr) hμ ha ht
end YM.TraceExtension.Photons
#print axioms YM.TraceExtension.Photons.regions_excludes
