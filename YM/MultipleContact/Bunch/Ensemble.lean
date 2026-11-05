import YM.MultipleContact.Bunch.Corridor
import YM.MultipleContact.Bunch.Summit
import YM.MultipleContact.Pair.Endpoint
/-! One common Wilson system with the pair prescriptions and additional
separated comparable-scale estimates for arbitrary finite arities. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.MultipleContact
open Function Set Metric MeasureTheory Power Direct Filter Table Extraction Spec Two TopologicalSpace
open scoped Topology ContDiff Distributions BigOperators Classical
open Bunching
variable {G:Gauge}

def ComparableProducts {C:Family G} (S:Table C.book) : Prop:=
    -- not simultaneous collapses; all exteriors strict vs. cluster, all inner gaps comparable
    ∀(n':ℕ) [_A:Inhabited (Fin n')](ι:Type*) [_B:Fintype ι] (n:ι→ℕ) (K:Set ((i:ι)→Points (n i))), IsCompact K → (∀z∈K,∀i, Points.cons 0 (z i)∈conf (n i+1)) →
    ∀(V:Fin n'→S.Tag)(q:∀i,Fin (n i)→ C.book.Token)(lamp:Lattice.Side),
       (∀ε> (0:ℝ), Puff K q V lamp (fun _ _=>True) (-(massOf V:ℝ)-ε)) ∧ ∀ h:ℕ,Puff K q V lamp (Local.silent q S h) (-(massOf V:ℝ)+h+1/64)
-- replace

theorem bunchSummit (G:Gauge)(hG:G.Simple){b:ℝ} (hb:0<b)(f:Order) :
    ∃(C:Family G)(g:Order)(T:Table C.book)(Z:Final C (f.refine g) T)(Q:Splitting Z.sector.derivatives)(D:∀k,Detector T k),
      C.Makes ∧ C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ Extraction.Wcmain C ∧ Q.Covariant Z.sector.turns Z.room.kernel.spin ∧ TwoPrescriptions Z.sector.derivatives Q D ∧ ComparableProducts T:=by
    obtain ⟨C,hB,hC,hM,hW,hT,h₀,H₁,hQ,hF⟩:= PhysicalNext.Repeat.Legato.noelWithBunches hG hb
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:=hF f; obtain ⟨hs,hV⟩:= hQ (f.refine g) s.copies
    obtain ⟨M,I,hI,p⟩:=MergeProof.Acme.emanate (W:=E) hT hG hs hV s hA.clean.ready hA.clean.tilt
    let X:Final C (f.refine g) T := Classical.choice (MergeProof.Acme.glistens hC hA.clean.ready hA.clean.tilt p)
    obtain ⟨Q,hQ⟩:=splits X.room.kernel X.phase.transport.injection X.phase.transport.rights X.phase.transport.spots
    let D(k:ℕ):Detector T k:= Classical.choice (detector_exists k T)
    refine ⟨C,g,T,X,Q,D,hM,hB,hC,hW,hQ,?_,?_⟩
    · intro u v ι hι U hU N hn; exact Two.e_pair (C:=C) (F:=f.refine g) ⟨hG,h₀,hT,X.room,X.phase.transport.injection,X.phase.transport.derivatives,X.sector.turns,X.phase.transport.motion⟩ u v Q D U hU N hn
    intro n i0 ι i1 nx K hK hsafe V q lamp
    exact ⟨manyOrdinary X.phase.transport.motion q V lamp K hK hsafe X.phase.transport.derivatives X.room.kernel X.room.generic X.room.copies hM hT H₁ hG,manySigned X.phase.transport.motion q V lamp K hK hsafe X.phase.transport.derivatives X.room.kernel X.room.generic X.room.copies hM hT H₁ hG⟩

example (G:Gauge)(hG:G.Simple) :∃(C:Family G)(g:Order)(T:Table C.book)(Z:Final C (Order.full.refine g) T), ComparableProducts T:=by
    obtain ⟨C,g,T,Z,Q,D,a,b,c,p,u,v,s⟩:=bunchSummit.{0,_} G hG two_pos Order.full; exact ⟨C,g,T,Z,s⟩
end YM.MultipleContact
