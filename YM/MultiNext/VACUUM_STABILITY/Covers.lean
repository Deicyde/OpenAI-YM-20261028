import YM.MultiNext.VACUUM_STABILITY.FirstGas

set_option warningAsError false

/-!
# Identity after the log on the covered gas, ordinary scalar version
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Restock
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V : Type} {n : Side} {G : Gauge} {B : Brush V G n} {C : Restock V G n}
variable {P : BudgetPoint} {L : V → Support n → Prop} {T : Finset V}

variable [Fintype V]




-- precisely which negative clusters were excluded
omit [Fintype V] in
private lemma target (D : Brush V G n) (C : Restock V G n) (P : BudgetPoint) (b : Finset ℕ) (i : D.Line) :
    (D.chapter i).zone ⊆ univ \ D.ban b ↔ ¬ (mill D C P).aimed b (.inl i) := by
  constructor
  · intro h hh; obtain ⟨k,hk,hK⟩:=hh
    obtain ⟨x,hx,hy⟩:=Finset.not_disjoint_iff.mp hK
    exact (mem_sdiff.mp (h hx)).2 (mem_biUnion.mpr ⟨k,hk,hy⟩)
  intro h y hy; apply Finset.mem_sdiff.mpr; refine ⟨mem_univ _,fun he => ?_⟩
  obtain ⟨k,hk,hK⟩:=mem_biUnion.mp he
  exact h ⟨k,hk,Finset.not_disjoint_iff.mpr ⟨y,hy,hK⟩⟩








end YM.Multi.Vacuum.Restock
