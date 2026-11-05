import YM.FullVolume.Finale.Program
import YM.EveryPhase.Extension

set_option autoImplicit false
noncomputable section

namespace YM.FullVolume.Verified
open YM.FullVolume.Final YM.Extraction
open YM.PhysicalNext.Repeat.Legato

/-- The same actual Wilson family supports full-mesh fixed-volume UV limits,
    a refined Final, and the accepted every-character reconstruction. -/
theorem uv_and_every_phase (G : Gauge) (h : G.Simple) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      R.family.path.levels.clock.kernel.penalty = δ ∧ Jewel R T W ∧
      ∀ f : Extraction.Order,
        ∃ (g : Extraction.Order) (S : Table R.family.book)
          (F : Spec.Final R.family (f.refine g) S),
          (Extraction.Order.mk Extraction.Sequence.full (f.refine g).per).Ordered R.family S ∧
          PositionsUV R.family Extraction.Sequence.full ∧
          ∃ L : YM.EveryPhase.Almanac F, YM.EveryPhase.Completed F L := by
  obtain ⟨R, T, W, hpenalty, J⟩ := YM.FullVolume.Final.july h δ hδ
  refine ⟨R, T, W, hpenalty, J, ?_⟩
  intro f
  obtain ⟨g, S, ⟨F⟩, hO⟩ := J.sampler f
  obtain ⟨L, hL⟩ := YM.EveryPhase.all_characters F
  exact ⟨g, S, F, hO, J.fullMesh, L, hL⟩

end YM.FullVolume.Verified
