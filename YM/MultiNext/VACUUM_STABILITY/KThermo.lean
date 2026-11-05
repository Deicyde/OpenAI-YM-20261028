import YM.MultiNext.VACUUM_STABILITY.Chapters

set_option warningAsError false

/-!
# Output forced data estimates at ALL ordinary parameter evaluations
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Restock
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V : Type} {n : Side} {G : Gauge} {B : Brush V G n} {C : Restock V G n}
variable {P : BudgetPoint} {L : V → Support n → Prop} {T : Finset V}

lemma ready_screws (h : Supported B C P L T) (i : Tail B) :
    Spanned P ((mill B C P).sites i) (screws B C P i).stamp.ink := by
  obtain i|i:=i
  · exact (Spanned.regular (B.chap_ok h i)).negate
  exact h.seals _



lemma glaze_pass (h : Supported B C P L T) (p) : Legible P ((mill B C P).remap p) (glaze B C P p).ink :=
  (mill B C P).remap_pass P (fun i => (B.d i).ink) (fun i => (screws B C P i).stamp.ink) h.stamp (ready_screws h) p



variable [Fintype V]





/-- Uniform per-evaluation combined charges needed for forced merger. -/
structure ReadyComb (B : Brush V G n) (C : Restock V G n) (P : BudgetPoint) (z : V→ℂ) (κ : ℝ)
    (f : ℕ→ℝ) (g : Tail B → ℝ) : Prop where
  onD i U : ‖(B.d i).tell z U‖ ≤ f i
  onM i U : ‖(screws B C P i).stamp.tell z U‖ ≤ g i
  owed : Ac.Hit (fun i => (B.pack i).zone) P.B f (Rates.inner P) (κ*Rates.window P)
  sold : Ac.Hit (fun i => (mill B C P).sites i) P.B g (Rates.inner P) (2*Rates.window P)



namespace ReadyComb
variable {κ : ℝ} {z : V→ℂ} {f : ℕ→ℝ} {g : Tail B → ℝ}


end ReadyComb


end YM.Multi.Vacuum.Restock
