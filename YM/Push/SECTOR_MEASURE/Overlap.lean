import YM.Push.SECTOR_MEASURE.Cells

/-!
# Obstruction check

The raw Plots cannot be used as a measurable set partition (E uses a
partition **of unity**). Not even modulo volume-null sets for live
tagged kernels, not even at the late price scales. Show the overcount
with the actual tags and Haar normalization.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure

open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory
 
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}

def voidStore (S : StepData c f) : Stores S := ⟨∅,∅,∅⟩





lemma exists_alive (hm : S.patch.Branches S.kernel G) (U : Config G f) : ∃ k, Alive S U k := by
  unfold Alive
  by_contra! h
  have hv : ∑ k, S.likelihood U k ≤ 0 := Finset.sum_nonpos fun k _ => h k
  rw [S.chosen hm] at hv; norm_num at hv







end YM.Push.SectorMeasure
