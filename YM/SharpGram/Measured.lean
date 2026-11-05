import YM.SharpGram.InContext
/-! Moving-frame Gram estimates on one Wilson family with OPE and reconstruction. -/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Function Set Filter Lattice RG Wilson Extraction Spec Org
open OPE OPE.Log Next.UVStress Weak
open scoped Topology BigOperators ContDiff
set_option quotPrecheck false
variable {G : Gauge}
theorem habitat (hG : G.Simple) {b : ℝ} (hb : 0<b) (f : Extraction.Order) :
    ∃ (C : Family G) (g : Extraction.Order) (T : Table C.book)
      (F : Spec.Final C (f.refine g) T) (L : EveryPhase.Almanac F)
      (P : Prescription F.sector.derivatives),
      C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty = b ∧
      UVExtension.Oasis.Floral (hG := hG) C ∧
      (Extraction.Order.mk Extraction.Sequence.full (f.refine g).per).Ordered C T ∧
      (∀ d k : ℕ, ∀ᶠ n in atTop,
        ∀ (r : ℕ) (v : Fin r → C.book.Token), (∀ i, (v i).1 ≤ d) →
          ∃ g, UVExtension.Poppy.Margins C r n k v g) ∧
      Facilities C (f.refine g) T ∧
      (∃ W r D, LogPackage C W r D ∧ TrueSteps C W) ∧
      EveryPhase.Completed F L ∧ AllShapes F P ∧
      Dense.Coverage C F.room.cutoff ∧
      -- all announced horizons, all sublimit choices in coverage on an arbitrary ultra
      (∀ U : Ultrafilter (ℕ×ℕ), (U : Filter _) ≤ (f.refine g).fuse → ∀ D : ℕ,
        Nonempty (Weak.Portfolio C F.room.cutoff D U) ∧
        ∀ X : Weak.Portfolio C F.room.cutoff D U,
          ∃ Y : ℕ → ∀ d : ℕ, YM.Spin.change T d,
          PricedIn F X Y ∧
          ∀ d : Fin (D+1), Tendsto (fun k => Weak.Portfolio.inBasis F X k d (Y k d)) atTop
                    (𝓝 (Weak.Portfolio.model C d))) := by
  obtain ⟨C,g,T,F,L,hc,ht,hB,hV,hK,hY,hW,hh,⟨h',hs⟩,hu,P,hP⟩:= common hG hb f
  refine ⟨C,g,T,F,L,P,hc,ht,hB,hV,hK,hY,hW,hh,hu,hP,hs,fun U hf D=>?_⟩
  exact ⟨fromCoverage hs U hf, fun X => attains F X hW hf⟩
end YM.SharpGram
