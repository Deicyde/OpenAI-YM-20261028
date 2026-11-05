import YM.SharpGram.Assembly.Flowers
import YM.OPE.ElementaryLog
import YM.EveryPhase.Extension
import YM.UVExtension.Reports.Ultraviolet

/-! A common Wilson family for the ultraviolet estimates, OPE services and reconstruction. -/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Filter Set Org MergeProof Spec UVExtension OPE OPE.Log

variable {G : Gauge}

/-- Keeps slack in order refinement. Matrix estimates so far independent of
order. -/
theorem coordination (hG : G.Simple) {b : ℝ} (hb : 0<b) :
    ∃ C : Family G, C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty=b ∧
      Oasis.Floral (hG:=hG) C ∧ Extraction.Wcmain C ∧
      (∀ d k : ℕ, ∀ᶠ n in atTop,
        ∀ (r : ℕ) (v : Fin r → C.book.Token), (∀ i, (v i).1 ≤ d) →
          ∃ g, Poppy.Margins C r n k v g) ∧
      (∃ W r D, LogPackage C W r D ∧ TrueSteps C W) ∧
      (∃ h:C.Makes, Dense.Coverage C h) ∧
      (∀ f, Cells.CellHyp C f → East.CompleteWeak C f) ∧
      ∀ F : Extraction.Order,
        ∃ (g : Extraction.Order) (T : Table C.book),
          (Extraction.Order.mk Extraction.Sequence.full (F.refine g).per).Ordered C T ∧
          Facilities C (F.refine g) T ∧ Nonempty (Final C (F.refine g) T) := by
  obtain ⟨C,h,hC,hM,hW,hS,H,cost,cover,hQ,hF⟩ := YM.PhysicalNext.Repeat.Legato.uv_log hG hb
  refine ⟨C,hM,hC,h,hS,hW,Poppy.bravo (Oasis.appears hS),cost,cover,fun f hp => (hQ f hp).2,fun F => ?_⟩
  obtain ⟨g,A,L,R,T,E,hA,s,hN⟩ := hF F
  obtain ⟨hs,hE⟩ := hQ (F.refine g) s.copies
  obtain ⟨M,I,hI,p⟩ := Acme.emanate (W:=E) H hG hs hE s hA.clean.ready hA.clean.tilt
  have F' := Acme.glistens hC hA.clean.ready hA.clean.tilt p
  obtain ⟨w,r,D,u,_⟩ := cost
  exact ⟨g,T,Reports.useFull hS F',⟨⟨hs,hG,⟨w,r,D,u.toPackage⟩,A,L,R,E,hA⟩,w,r,D,u⟩,F'⟩

/-- One witness supplying both previous contracts and poised for the sharp
OPE result. Does not assume new comparison or log bound. -/
theorem common (hG : G.Simple) {b : ℝ} (hb : 0<b) (f : Extraction.Order) :
    ∃ (C : Family G) (g : Extraction.Order) (T : Table C.book)
      (F : Spec.Final C (f.refine g) T) (L : EveryPhase.Almanac F),
      C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty = b ∧
      UVExtension.Oasis.Floral (hG := hG) C ∧
      (Extraction.Order.mk Extraction.Sequence.full (f.refine g).per).Ordered C T ∧
      (∀ d k : ℕ, ∀ᶠ n in atTop,
        ∀ (r : ℕ) (v : Fin r → C.book.Token), (∀ i, (v i).1 ≤ d) →
          ∃ g, UVExtension.Poppy.Margins C r n k v g) ∧
      Facilities C (f.refine g) T ∧
      (∃ W r D, LogPackage C W r D ∧ TrueSteps C W) ∧
      (∃ h:C.Makes, Dense.Coverage C h) ∧
      EveryPhase.Completed F L ∧
      ∃ P : Prescription F.sector.derivatives, AllShapes F P := by
  obtain ⟨C,hm,hC,hb,hV,hW,hr,hs,cover,h,X⟩ := coordination hG hb
  obtain ⟨g,T,hf,hV0,⟨U⟩⟩ := X f
  obtain ⟨L,ht⟩ := EveryPhase.all_characters U
  obtain ⟨P,hP⟩ := Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection
  exact ⟨C,g,T,U,L,hm,hC,hb,hV,hf,hr,hV0,hs,cover,ht,P,hV0.toServices.everything U P hP⟩
end YM.SharpGram
