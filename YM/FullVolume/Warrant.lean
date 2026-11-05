import YM.Extra.FREE_DETECTOR_ALGEBRA.Vane
import YM.MergeProof.SteamW
import YM.MergeProof.Thrush
import YM.Next.RANK.Beam
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Star



/-! Vote-to-Rank. Stop after Seed (Basis, Spans, Cleaner, corrected, actual Rank matrix). -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G} {S:Table C.book} {D:Bin S} {F:Extraction.Order}
theorem warrant (M : C.Makes) (hg:G.Simple)
    {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (he:Scrim C W u ψ φ δ (fly C.path.levels) r D)
    {O : HaarBudget G} (Q : ∀ d:ℕ,Tapes.Panel d) (H:∀ i:ℕ,0 ≤ generator G i)
    (J : ChartRatio G) {B:PhysicalNext.RankCovariance.Binding C}
    (hr:∀ i:ℕ, ∃ᶠ j:ℕ in atTop, let v:= (Q i).patronize C (H i); Tender v j ∧ Metering v O j (-3) ∧ (∃ l r, ShowHours J B (v.current j) j (-3) l r ∧ Vents B (v.current j) J l r j)) : ∀ S:Table C.book, ∀ d,∃ (X: Columns C S d)(Y: X.Trials), Market.Purchases Y := by
   intro S
   let X(d:ℕ): Columns C S d:= Extra.FD.vane C S (Extra.FD.recorded C.labels d) _ _ Extra.FD.vane_possible
   have ht (d:ℕ): ∃ Z : (X d).Trials, Market.Purchases Z:=by
      let Ξ := (Q d).patronize C (H d)
      obtain ⟨p⟩:=Next.Rank.Price.from_labels C (X d)
      have hx : ∃ᶠ k in atTop, Tender Ξ k∧ Metering Ξ O k (-3)∧ (∃ l r, ShowHours J B (Ξ.current k) k (-3) l r ∧ Vents B (Ξ.current k) J l r k)∧ LanternMarks M Ξ (X d) k:=by
        refine ((hr d).and_eventually (bursts C (O:=O) (e := -3) d M hg he.1 he.2 (X d) Ξ rfl le_rfl)).mono ?_
        rintro k ⟨⟨T,H,hV⟩,hh⟩; exact ⟨T,H,hV,hh H⟩
      obtain ⟨Z,h,hZ⟩:= Soft.wheeled M Ξ (X d) O p hg (Soft.cast_off B M J Ξ (X d) (w:=-3) hg hx)
      exact ⟨Z,hZ⟩
   intro d; exact ⟨X d,ht d⟩
end YM.MergeProof.Accent
