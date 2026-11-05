import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Merge
import YM.Extraction.Integrate

set_option warningAsError false

/-!
# Change a mask without assuming a new formula at flagged fields

often needed *between* taking the log and testing the
jets in a proposed output. General attaching-letter expenditure & a
concrete indicator-conversion corollary (later below). First part
agnostic to mask shapes; requires Exact identity on V up to a
summable sum of corrections supported near actual flags (so ANY old K
family will cover an incident site or else be zero). Use only after
establishing this pre-assembly difference estimate. Applies even at
winding stencils, empty sector and if a correction depends on several
flags in its reads (it's counted once). No cumulative stability claim.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.MaskMotion
open Lattice RG Wilson Finset Filter Function
open AbsoluteSums AbsoluteSums.Ursell Attach AbsoluteSums.Multiple AbsoluteSums.Trees
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {ι κ : Type*} {n : Side} {G : Gauge}
variable (Y Y1 I : κ → Support n) (X X1 : ι → Support n) (D : Support n)



def diff (p : BudgetPoint) (F : ι → Config G n → ℝ) (i : ι) (V : Config G n) :=
    masked p.threshold (X1 i) (F i) V - masked p.threshold (X i) (F i) V



lemma diff_used (p : BudgetPoint) (F : ι → Config G n → ℝ) (i : ι) (he : X i⊆X1 i) (h : p.Regular (X i) (F i)) :
    Measurable (diff X X1 p F i) ∧ UsesFinal p.threshold (X1 i) (diff X X1 p F i) ∧ GaugeInvariant (diff X X1 p F i) := by
  refine ⟨(masked_measurable _ _ _ h.borel).sub (masked_measurable _ _ _ h.borel),fun V W H hF => ?_,fun t V => ?_⟩
  · have ht (P : Support n) (hv : P⊆X1 i) : masked p.threshold P (F i) V = masked p.threshold P (F i) W := by
      have hi : Healthy p.threshold P V ↔ Healthy p.threshold P W := by
        unfold Healthy; simp_rw [Finset.disjoint_iff_inter_eq_empty]
        have hh : P ∩ RG.flags p.threshold V = P ∩ RG.flags p.threshold W := by
          ext x; simp only [mem_inter]; apply and_congr_right; intro j
          have hh := Iff.of_eq (congr_arg (fun P => x∈P) hF); simp only [Finset.mem_inter,hv j,true_and] at hh; exact hh
        rw [hh]
      by_cases hh : Healthy p.threshold P W
      · rw [masked_eq _ _ _ _ hh,masked_eq _ _ _ _ (hi.mpr hh)]; exact h.sites _ _ (agrees_mono H he)
      rw [masked_ne _ _ _ _ hh,masked_ne _ _ _ _ (mt hi.mp hh)]
    exact congr_arg₂ (· - ·) (ht _ (Subset.refl _)) (ht _ he)
  have hh (P : Support n) : masked p.threshold P (F i) (Lattice.gauge t V) = masked p.threshold P (F i) V := by
    have he : Healthy p.threshold P (Lattice.gauge t V) ↔ Healthy p.threshold P V := by unfold Healthy; rw [gauge_flags]
    by_cases ht : Healthy p.threshold P V
    · rw [masked_eq _ _ _ _ (he.mpr ht),masked_eq _ _ _ _ ht]; exact h.symmetry ..
    rw [masked_ne _ _ _ _ ht,masked_ne _ _ _ _ (mt he.mp ht)]
  exact congr_arg₂ (· - ·) (hh _) (hh _)



/- Exclusion estimates when the letter footprint has just been enlarged.
Payment on X1, Y1 and strength `A+δ` needed. N is extraction e.g.
from compulsory marks (keep ≥0). -/
section Bound
variable (w : κ → ℝ) (b : ι → ℝ)
def lexer (i : Species' Y1 X1) :=
    Multiple.manyW (Sum.elim w b) i.val.val






end Bound
end YM.Push.LogIdentity.MaskMotion
