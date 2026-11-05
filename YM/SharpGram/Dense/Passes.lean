import YM.SharpGram.Dense.Cover
/-! Public geometry form, with SAME function g for all horizons and
with the real `charts` of `Poised`. g k needn't equal k; it is a
late-close predecessor useful for transporting quotas. -/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Dense
open Function Set Filter Asymptotics Lattice RG Supply Next.Rank Next.Rank.Ship
open Pert.Dense Tapes PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft Input Precision
open MeasureTheory MergeProof.East
open scoped Topology BigOperators
variable {G : Gauge} {s : Sheet G} {w : Rolls s}
  {θ : Protection w} {H : Delays θ} {Y : Bar H} {U V : Wait Y}
variable {C : Family G}
-- exact hypotheses for later weak comparison. use A.measure only no separated tie workaround.
structure Coverage (C : Family G) (h : C.Makes) : Prop where
  holds : ∃ (B : MapPrices) (O : HaarBudget G) (J : ChartRatio G)
    (K : Binding C) (P : ∀ d, Fin 3 → Tapes.Panel d) (cost : ℕ → ℝ) (g : ℕ → ℕ),
      -- don't assert local costs in lieu of Poised. Keep arcs as fixed per D.
      K.prices=B ∧ (∀ d, ∃ ξ, Checks (P d 0).arc (P d 1).arc (P d 2).arc ξ (trays d) d) ∧
      (∀ d i, i ≤ d → MergeProof.Accent.generator G i ≤ cost d) ∧
      Tendsto g atTop atTop ∧
      (∀ᶠ k in atTop, g k ≤ k ∧ C.S.scale k ≤ C.S.scale (g k) + Real.log (C.path.levels.clock.hatBeta k)) ∧
      ∀ d, ∀ᶠ k in atTop, ∃ Y, Poised (P d) K h O J (trays d) (cost d) (g k) Y

lemma covered (B : MapPrices)(O : HaarBudget G) (J : ChartRatio G) (V0 : StationPort U B O J)
    (hp : V0.Certified) (hs : U.window = slim Y) (ha : LateEnough U V)
    (hv : Paid V C.path.levels) (K : Binding C) (he : K.prices=B)
    (h : C.Makes) (ht : Next.Rank.East.ParadeX C) : Coverage C h := by
  obtain ⟨g,hg,hh⟩:= nearby hs ha hv
  refine ⟨B,O,J,K,V0.panels,V0.cost,g,he,hp.signs,hp.reasonable,hg,
    hh.mono (fun i hi => ⟨hi.1,hi.2.2⟩),fun d =>?_⟩
  exact (hh.and (hg.eventually (hp.orders C (ha.1.retain hv) K he h ht d))).mono (fun i hi => hi.2 hi.1.2.1)
end YM.SharpGram.Dense
