import YM.MultipleContact.Multi.Score
import YM.MultipleContact.Bunch.Ensemble
/-! Simultaneous signed bound at arbitrary ratios in distinct strict collars. This is not an assumption on a substituted family. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.MultipleContact
open Extraction Spec Two Table Bunching
open Filter Set Function
open scoped Topology BigOperators Classical ContDiff

theorem joinedSummit (G:Gauge)(hG:G.Simple){b:ℝ} (hb:0<b)(f:Order) :
    ∃(C:Family G)(g:Order)(T:Table C.book)(Z:Final C (f.refine g) T)(Q:Splitting Z.sector.derivatives)(D:∀k,Detector T k),
      C.Makes ∧ C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ Extraction.Wcmain C ∧ Q.Covariant Z.sector.turns Z.room.kernel.spin ∧ TwoPrescriptions Z.sector.derivatives Q D ∧ ComparableProducts T ∧ ∀ m:ℕ, Joins.Store T m:=by
    obtain ⟨C,hB,hC,hM,hW,hT,h₀,H₁,hQ,hF⟩:= PhysicalNext.Repeat.Legato.noelWithBunches hG hb
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:=hF f; obtain ⟨hs,hV⟩:= hQ (f.refine g) s.copies
    obtain ⟨M,I,hI,p⟩:=MergeProof.Acme.emanate (W:=E) hT hG hs hV s hA.clean.ready hA.clean.tilt
    let X:Final C (f.refine g) T := Classical.choice (MergeProof.Acme.glistens hC hA.clean.ready hA.clean.tilt p)
    obtain ⟨Q,hQ⟩:=splits X.room.kernel X.phase.transport.injection X.phase.transport.rights X.phase.transport.spots
    let D(k:ℕ):Detector T k:= Classical.choice (detector_exists k T)
    refine ⟨C,g,T,X,Q,D,hM,hB,hC,hW,hQ,?_,?_,?_⟩
    · intro u v ι hι U hU N hn; exact Two.e_pair (C:=C) (F:=f.refine g) ⟨hG,h₀,hT,X.room,X.phase.transport.injection,X.phase.transport.derivatives,X.sector.turns,X.phase.transport.motion⟩ u v Q D U hU N hn
    · intro n i0 ι i1 nx K hK hsafe V q lamp
      exact ⟨manyOrdinary X.phase.transport.motion q V lamp K hK hsafe X.phase.transport.derivatives X.room.kernel X.room.generic X.room.copies hM hT H₁ hG, manySigned X.phase.transport.motion q V lamp K hK hsafe X.phase.transport.derivatives X.room.kernel X.room.generic X.room.copies hM hT H₁ hG⟩
    exact Joins.fills hT H₁ X.room.copies X.room.generic X.room.kernel X.phase.transport.derivatives hM X.phase.transport.motion hG
end YM.MultipleContact
