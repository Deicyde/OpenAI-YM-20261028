import YM.AnalyticNext.GRID_STOP_ATTENUATION.Annual
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.PMOM
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Path
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOCAL_SPLITTING.Atoms
import YM.Push.LOCAL_SPLITTING.Leading


/-! # Apply PMOM's projection nulls and chosen powers at the literal
stencils, to buy the EXCEPTIONAL address cost.

Can actually apply also to canonical inputs at their orders, no k+1 loss
on long etc. This is before multiplying by the engineering factor. Does not
infer projection-coordinate agreement from a bound on projected f! Separate
small errors to be paid with comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GridRenewal.Speed
open Function Filter MeasureTheory RG Wilson Lattice Labels Source Precision Laurent Exterior
open Bid Next.Foundations MultiNext.SignedSource Push.Local
open    Mom   
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {c n : Side} {d k : ℕ} {F : Frame G d}

lemma grade_grows (i : F.Index) (h : i≠0) : 1 ≤ (F.grades i).1 := by
  have hl := F.factors_pos i h
  have hy := F.basis.ne_zero i
  let p := F.basis i
  have he : MvPolynomial.support p.val ≠ ∅ := by
    exact mt MvPolynomial.support_eq_empty.mp (fun h => hy (Subtype.ext h))
  obtain ⟨j,hj⟩:=Finset.nonempty_iff_ne_empty.mpr he
  have hK : Finsupp.weight bidegree j=F.grades i := (pure_grade _ p).1 (F.pure i) (MvPolynomial.mem_support_iff.mp hj)
  have hv := power_le j; rw [hK, ← show (F.grades i).1=height j from congrArg Prod.fst (hK.symm.trans (weight_slot _))] at hv; omega

lemma canon_first (o : Site n) {i : F.Index} (hi : i≠0) {P : BudgetPoint} {A : Hol G} {H : SectionData F} {w : ℝ}
    (he : Readable A H P n w) :
    ∀ j : Jet G,∀ b : ℕ,b ≤ (F.grades i).1-1 → iteratedDeriv b (fun t=> presented H o P.threshold (column F i) (A.testLinks d o j t)) 0=0 := by
  intro j b hb
  have hx := he.fit
  let z := F.scaled P.threshold⁻¹ (column F i)
  have ht := placed_reads H o hx he.sound z
  unfold Reads at ht; rw [if_pos (nonwrapping_placement _ _ hx)] at ht
  have hB : b < (F.grades i).1 := by have hv:= grade_grows i hi; omega
  apply ((ht j).2.2 b (hB.le.trans (F.bound i))).trans
  apply label_reads (x:=(F.grades i).1) (y:=(F.grades i).2) _ j b hB
  change F.coords.symm z ∈ Grade (F.grades i)
  unfold z; rw [show column F i=F.coords (F.basis i) from (F.coords_basis i).symm, F.scaled_pure _ _ (F.pure i),map_smul,F.coords.symm_apply_apply]; exact (Grade _).smul_mem _ (F.pure i)









end YM.GridRenewal.Speed
