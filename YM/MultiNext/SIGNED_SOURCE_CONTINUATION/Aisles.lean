import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Body
import YM.Next.SCHEDULE.Postal

set_option warningAsError false

/-!
# Accountable regular moves *within* the old dictionary
We add a sufficiency gate on the C producer. At requested reference weights,
the regular support sequence of its columns should have room for all possible
stencils at the origin, with repetitions (design before Paper starts by
padding the regular support sequences, including for columns vanishing at
those addresses). No such property needed of vacuum additive labels.
Do not perform reindexing of the given transfer data! This file licenses
moving NEW regular coefficients into those open slots, preserving budgets.
Force is already indexed globally (budgets summed at actual indices there).

A key case is the existing relay's `combine`: at a lower
continuation scale, when supports of both sources agree in the same table,
using this literal definition for getting `LocalBounds` doesn't destroy the
signed cancellations; both estimates on the old addresses and ones on the
`combine` table mean the same thing after this step.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource
open Function Filter MeasureTheory RG Wilson Lattice Labels Source
open Push.RelayDifference
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side} {e : ℕ} {F : Frame G e} {R : Rep G n} {o : Site n} {A : Hol G}
open Body
variable {U V : GridU n}

def Bays (U : GridU n) (o : Site n) := ∀ X : Support n, o ∈ X → Set.Infinite {i | U i=X}



section Basic
variable {α β γ : Type*} (f : α ↪ β)
open scoped Classical in
def hang [Zero γ] (w : α → γ) (i : β) : γ := if h : i∈Set.range f then w (Classical.choose h) else 0
lemma hang_at [Zero γ] (w : α → γ) (i : α) : hang f w (f i)=w i := by
  unfold hang; split
  next h => rw [f.injective (Classical.choose_spec h)]
  next he => exact False.elim (he ⟨i,rfl⟩)
lemma hang_out [Zero γ] (w : α → γ) (i : β) (h : i∉Set.range f) : hang f w i=0 := by
  unfold hang; split
  next he => exact False.elim (h he)
  rfl
lemma budget_of_hang {g : α→ℝ} {v} (h : SumBudget g v) : SumBudget (hang f g) v := by
  have hs := (f.injective.hasSum_iff (hang_out f g)).mp (show HasSum _ (∑' i,g i)
    from by rw [show (hang f g) ∘ f=g from funext (hang_at f g)]; exact h.2.1.hasSum)
  refine ⟨fun i => ?_,hs.summable,hs.tsum_eq.trans_le h.2.2⟩
  by_cases he : i ∈ Set.range f
  · obtain ⟨j,rfl⟩ := he; rw [hang_at]; exact h.1 j
  rw [hang_out f _ _ he]

end Basic



section Scaffold
variable {κ r : ℝ}
variable {D : Body F n} {f : ℕ ↪ ℕ} (h : ∀ i,V (f i)=U i)
include h








end Scaffold









end YM.MultiNext.SignedSource
