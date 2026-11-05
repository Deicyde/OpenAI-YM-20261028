import YM.OPE.Subpower
import YM.OPE.Log.Entrance

/-! Constructed OPE services and the common schedule for the finite-grade expansions. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Lattice RG Log Next.Extract Dash Org Bid OS Ground Spec MergeProof
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}

structure Facilities (C:Family G)(F:Extraction.Order)(S:Table C.book) : Prop extends Services C F S where
    costlier : ∃ W r D, LogPackage C W r D
lemma Facilities.establishment (h:G.Simple){b:ℝ}(hb:0<b)(f:Extraction.Order) : ∃ C:Family G,C.path.levels.clock.kernel.penalty=b ∧ ∃ (t:Extraction.Order)(S:Table C.book), Facilities C (f.refine t) S ∧ Nonempty (Final C (f.refine t) S):=by
    obtain ⟨C,hB,hC,hM,hW,hS,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.noel_planned h hb
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
    obtain ⟨hs,hG⟩:= hQ (f.refine g) s.copies
    obtain ⟨M,I,hI,p⟩:=Acme.emanate (W:=E) H h hs hG s hA.clean.ready hA.clean.tilt
    refine ⟨C,hB,g,T,⟨⟨hs,h,?_,A,L,R,E,hA⟩,hS⟩,Acme.glistens hC hA.clean.ready hA.clean.tilt p⟩; obtain ⟨w,z,Z,u⟩:= hS; exact ⟨w,z,Z,u.toPackage⟩

theorem prepared (G:Gauge)(h:G.Simple){b:ℝ}(hb:0<b)(f:Extraction.Order) : ∃ C:Family G,C.path.levels.clock.kernel.penalty=b∧ ∃ (t:Extraction.Order)(S:Table C.book), Facilities C (f.refine t) S ∧ ∃ (U:Final C (f.refine t) S) (P:Prescription U.sector.derivatives), AllShapes U P:=by
    obtain ⟨C,hC,g,S,hV,⟨U⟩⟩:= Facilities.establishment h hb f; obtain ⟨p,hp⟩:= Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection
    exact ⟨C,hC,g,S,hV,U,p,hV.toServices.everything U p hp⟩
end YM.OPE
