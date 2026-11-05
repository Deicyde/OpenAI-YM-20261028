import YM.MergeProof.Emanate
import YM.TraceExtension.Made.Noel
import YM.MergeProof.Summit



set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Acme
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Cells Spec
open Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge}
lemma northBay (h:G.Simple)(b:ℝ)(hb:0<b) (f:Extraction.Order) :∃ C:Family G,C.Makes∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧ ∃ (g:Extraction.Order) (T:Table C.book), (∃ s:Seed C (f.refine g) T, Maxwell.Ranks T s.kernel.spin)∧ (∃ (M:MaxwellData C)(I:IR (C:=C) T)(V:DiffPlan T), I.J≠0∧UV C (f.refine g) T V M I)∧ Trace.Over.Gallery C (f.refine g) ∧ Nonempty (Final C (f.refine g) T):=by
    obtain ⟨C,hB,hC,hM,hW,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.noelT h hb
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
    obtain ⟨hs,hG,hP⟩:= hQ (f.refine g) s.copies
    obtain ⟨M,I,hI,p⟩:=emanate (W:=E) H h hs hG s hA.clean.ready hA.clean.tilt
    exact ⟨C,hM,hC,hB,hW,g,T,⟨s,hN⟩,⟨M,I,E,hI,p⟩,hP,glistens hC hA.clean.ready hA.clean.tilt p⟩
end YM.MergeProof.Acme
#print axioms YM.MergeProof.Acme.northBay
