import YM.MultipleContact.Pair.Extension
import YM.MultipleContact.Matching.Choice
import YM.MergeProof.Summit

/-! Keeping the same baseline system and all the detector/filtration data for the two-point result. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MultipleContact
open Function Set Metric MeasureTheory Power Direct Filter Table Extraction Spec Two TopologicalSpace
open scoped Topology ContDiff Distributions BigOperators Filter Classical
variable {G:Gauge}

-- Type* universe for number of exterior requests. Finite horizon first; fixed choices for all requests.
def TwoPrescriptions {C:Family G}{S : Table C.book} (P:DiffPlan S) (Q:Splitting P)(D:∀ h,Detector S h):Prop := ∀A B:S.Tag, ∀(ι:Type*) [_F:Fintype ι](U:ι→Profile C.book),Eligible U→∀N:ℕ, massDeg A B-4≤N→
  ∃r> (0:ℝ),
   (∀ V:Opens E4, ∀t∈targets S (includeIndexes D N U),∀s:ℝ, 0<s → ∃X:𝓓(V,ℂ) →L[ℂ] ℂ, (∀f:𝓓(V,ℂ),X f=rule Q D r s (massDeg A B) (measurePair A B) t f) ∧
       ∀f:𝓓(V,ℂ), tsupport f⊆ball 0 r \ {0} → X f=∫ y:E4, f y * measurePair A B t y) ∧
       (∀ε:ℝ,0 < ε → Rate (-(massDeg A B:ℝ)-ε) (1+massDeg A B) (targets S (includeIndexes D N U)) (fun s=>rule Q D r s (massDeg A B) (measurePair A B))) ∧
       (∀h:ℕ,h≤N → ∃ γ:ℝ,0<γ ∧ Rate (h-(massDeg A B:ℝ)+γ) (1+massDeg A B) (targets S (includeIndexes D N U)) (fun s t f=>extMiss Q D r s (massDeg A B) h (measurePair A B) t f)) ∧
       (∀h:ℕ,h≤N → ∀w:ℕ, w≤h → ∃γ:ℝ,0<γ ∧ ReadRate w (1+massDeg A B) ((w:ℝ)-1-(massDeg A B:ℝ)+γ) (fun s f=>Q.part w h (readExtended Q D r s (massDeg A B) h (measurePair A B) f)))


-- Still choose any positive b and any initial extraction; no changed family per A,B,horizon,tolerance.
theorem pairSummit (G:Gauge)(hG:G.Simple){b:ℝ} (hb:0<b) (f:Order): ∃ (C:Family G)(g:Order)(T:Table C.book)(Z:Final C (f.refine g) T) (Q:Splitting Z.sector.derivatives) (D:∀k,Detector T k),
   C.Makes ∧ C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ Extraction.Wcmain C ∧ Q.Covariant Z.sector.turns Z.room.kernel.spin ∧ TwoPrescriptions Z.sector.derivatives Q D:=by
    obtain ⟨C,hB,hC,hM,hW,hT,H₀,hQ,hF⟩:= PhysicalNext.Repeat.Legato.noelCoordinates hG hb
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
    obtain ⟨hs,hV⟩:= hQ (f.refine g) s.copies
    obtain ⟨M,I,hI,p⟩:=MergeProof.Acme.emanate (W:=E) hT hG hs hV s hA.clean.ready hA.clean.tilt
    let X:Final C (f.refine g) T := Classical.choice (MergeProof.Acme.glistens hC hA.clean.ready hA.clean.tilt p)
    obtain ⟨Q,hQ⟩:=splits X.room.kernel X.phase.transport.injection X.phase.transport.rights X.phase.transport.spots
    let D(k:ℕ):Detector T k:= Classical.choice (detector_exists k T)
    refine ⟨C,g,T,X,Q,D,hM,hB,hC,hW,hQ,?_⟩
    intro u v ι hι U hU N hn
    exact Two.e_pair (C:=C) (F:=f.refine g) ⟨hG,H₀,hT,X.room,X.phase.transport.injection,X.phase.transport.derivatives,X.sector.turns,X.phase.transport.motion⟩ u v Q D U hU N hn

-- Explicit embedding of the old Prop, no assumptions, plus unselected correlations.
theorem fromPair : YM.Spec.CLOSED:=fun G h=> by obtain ⟨C,g,T,X,-,-,-⟩:=pairSummit.{0} G h one_pos Order.full; exact ⟨C,Order.full.refine g,T,⟨X⟩⟩
end YM.MultipleContact
