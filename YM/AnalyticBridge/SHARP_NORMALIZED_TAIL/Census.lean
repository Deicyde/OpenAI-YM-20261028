import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Packets

/-!
# The core energy read

An extra obligation if charging annuluses even on the growth probe.
Discharge on concrete frozen Y positions and k. Retain the tests for V
(like output flags -- V coincides in this license). The selector on
**all** plaquettes also has to agree; use the exponentially relaxed
threshold. Predictions include fallback outcome and turns use exactly
`carry`. Not for the full uncut beta tail!
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Drain
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Tree MeasureTheory
open Next.Fluctuations Next.SectorChange SectorNext.Vacuum.ReLog
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented Finset Inventory Almanac Presented
open Precision Exterior SectorNext.Remainder SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius YM.Push.SectorMeasure

variable {c f : Side} {G : Gauge} {x W : ℝ} {S : StepData c f} {T : Tube G S} {P : Teller G}
  {R : Rep G f} {D : Allocation G S x W} {F : Forest S.ratio} {V : Config G c} {L : Almanac T D R F}

structure Dirigible (T : Tube G S) (x : ℝ) : Prop where
  size : 10 ≤ radiusB x
  pred : predReach S.patch ≤ radiusB x
  envelope : ∀ k : ℕ, fiery G x S.patch.L*Real.exp (k/T.high.relaxation)<2 → k+1 ≤ radiusB x/50





private lemma arc {a b : Site c} {d r u : ℕ} {O : Stores S} (h : a∈O.dome d)
    (ht : separation a b ≤ u) (hx : d+u ≤ r) : b∈O.dome r := by
  obtain ⟨i,hi,h⟩ := halo_spec.mp h
  exact halo_spec.mpr ⟨i,hi,(separation_triangle ..).trans ((add_le_add h ht).trans hx)⟩

lemma shiftedQ (i : Bond c) (s : Signed) : separation (s.act i.1) (sendEdge s 0 i).1 ≤ 1 := by
  unfold sendEdge Step.used; split
  · have ht := Work.E03.sep_step ((s.act i.1)-step (s.perm i.2)) (s.perm i.2)
    simp only [affine, add_zero, Step.rotate,posDir]
    rw [sub_add_cancel,separation_comm] at ht; exact ht
  simp [affine]



lemma pred_tags {U : Config G f} {k l : S.Choices} {X : Support c} (h : Tags.Synchronized X k l)
    (i : Bond c) (hx : i.1∈X) (hy : i.1+Lattice.step i.2 ∈ X) : S.prediction U k i=S.prediction U l i := by
  have he : S.connector U k.1 i = S.connector U l.1 i := funext fun t => by
    unfold StepData.connector StepData.frames; rw [h.1 i.1 hx,h.1 _ hy]
  unfold StepData.prediction
  rw [h.2 i hx hy,he]





end YM.AnalyticBridge.Sharp.Drain
