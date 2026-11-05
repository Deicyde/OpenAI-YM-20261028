import Mathlib.Analysis.Normed.Group.Tannery
import YM.Progress.DIRECTED_RECIPE.Pellets
import YM.Work.H01
import YM.Work.H02
import YM.Work.H03






/-!
# Pre-assembly representation

`Ingredients` is an invoice to the separate estimation tasks (before combining
soft with preliminary hard), not the result of a projection from a Schedule.
Same form serves initial and output packing. Consume verified H01--03 (also
H04 where applicable) to actually assemble E/K, with *the same* estimates
through the fixed alphabet. β in the fit is always the local scale's scalar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG Wilson Lattice RG.Shoot Ovens Ovens.Pipes Rack
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {X : Pipes G n} {d : Tap G n} {P : BudgetPoint} {δ w : ℝ}

/-- Needs joint indexed summability (including old and new predicates at their
supports; soft attaches at actual flags; +1 reserve on this merger). -/
structure Ingredients (X : Pipes G n) (d : Tap G n) (P : BudgetPoint) (δ w : ℝ) : Prop where
  pays : ∃ κ γ u, Digests X d P δ u ∧ X.Buys d P κ γ ∧ Bid.quote κ γ ≤ w

/-- Output exponent before these attachments/merger. This rep has NOT been
readdressed. -/
def trunk (W : PathData G) (c : Clip) (P : BudgetPoint) (X : Pipes G n) (d : Tap G n) (β v : ℝ) : Rep G n :=
  ⟨W,c,X.pours d,P,β,v⟩

/-- Same operation at every scale, both in startup and in return. -/
def finish (W : PathData G) (c : Clip) (P : BudgetPoint) (X : Pipes G n) (d : Tap G n) (β v : ℝ) : Rep G n :=
  ⟨W,c,fused (folio G n) P (widen X d),P,β,v⟩



namespace Ingredients
variable (H : Ingredients X d P δ w)
include H

lemma to_shelves : Ingredients (drawer G n) (widen X d) P δ w := by
  obtain ⟨κ,γ,u,he,hp,hg⟩ := H.pays
  exact ⟨κ,γ,u, absorbs he,sells hp,hg⟩

lemma address (W : PathData G) (c : Clip) (β v : ℝ) (F : ℕ ≃ X.Pellet) :
    Readdress P (upE X) (nameUp F) (fused F P d) (finish W c P X d β v).activities := by
  obtain ⟨κ,γ,u,H,_,_⟩ := H.pays
  exact lift_fused H F

lemma spare_room (W : PathData G) (c : Clip) (β v : ℝ) : HasSlots P (finish W c P X d β v).activities := by
  obtain ⟨κ,γ,u,H,_,_⟩ := H.pays
  exact never_spent H

lemma gates (W : PathData G) (c : Clip) (β v : ℝ) :
    (finish W c P X d β v).activities.Valid P δ w := by
  obtain ⟨κ,γ,u,he,hp,hg⟩ := H.to_shelves.pays
  obtain ⟨ha,hb⟩ := Work.H03.answer _ n _ _ (folio G n) _ _ _ he
  refine ⟨?_,ha,hb,he.stamp.boundE,Work.H02.answer _ n _ _ (folio G n) _ _ κ γ _ _ hg he hp⟩
  exact ⟨he.stamp.regular.smooth,he.stamp.regular.at_flat,he.stamp.regular.vanish⟩

lemma unshifted (W : PathData G) (c : Clip) (β v : ℝ) (U : Config G n) :
    (finish W c P X d β v).eval U = (trunk W c P X d β v).eval U * Real.exp (∑' i, d.logarithm i U) := by
  obtain ⟨κ,γ,u,he,hp,_⟩ := H.to_shelves.pays
  have hx := preserves X d P
  have hs := Work.H01.answer _ n _ _ (folio G n) _ _ κ γ _ he hp U
  simp only [Rep.eval]
  have ht : (finish W c P X d β v).exponent U = (trunk W c P X d β v).exponent U := by
    change v * _ - (W.inChannels _ P β _) - ((drawer G n).pours (widen X d)).additive P U =
      v * _ - _ - _
    rw [hx.same_sum]; rfl
  rw [ht]; dsimp only [finish,trunk]
  rw [hs, same_log, hx.same_gas,mul_assoc]

lemma exact_eval (W : PathData G) (c : Clip) (β v : ℝ) (U : Config G n) :
    (finish W c P X d β v).eval U = Real.exp (v * Fintype.card (Site n)) *
      ((trunk W c P X d β 0).eval U * Real.exp (∑' i, d.logarithm i U)) := by
  rw [H.unshifted]
  have ht : (trunk W c P X d β v).exponent U = v * Fintype.card (Site n) + (trunk W c P X d β 0).exponent U := by
    unfold trunk; dsimp only [Rep.exponent]; ring
  rw [Rep.eval, Rep.eval, ht, Real.exp_add]
  dsimp only [trunk]; ring
end Ingredients
end YM.Progress.DirectedRecipe
