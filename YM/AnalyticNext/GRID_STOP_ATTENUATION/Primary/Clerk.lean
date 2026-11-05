import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Bid.Drops
import YM.Next.MULTISOURCE.Curves
import YM.Org.Theatre
import YM.Work.A05.Read

set_option warningAsError false

/-! Single placement on a true pack alphabet. Incoming entries may retain
summable-many; allocation itself can be finite. Keep *all* unmarked entries.
Important for joint output as well as for remainder readout. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Primary
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Finset
open Multi.Couples
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {n : Side} {G : Gauge} {P : Rep G n} (hP : Room P)

abbrev slot (p : Pack n) := (hP p).choose
lemma address (p : Pack n) : Pack.ofAddress P.activities (slot hP p)=p := (hP p).choose_spec.1
lemma check (p : Pack n) (U : Config G n) (he : p.zone ∩ flags P.p.threshold U=p.flagsAt) :
    (P.activities.forced (slot hP p)).extraTest U := (hP p).choose_spec.2 _ he
lemma check_inj : Injective (slot hP) := fun p q h => (address hP p).symm.trans ((congr_arg _ h).trans (address hP q))

def allocate {I : Type*} [Zero I] (F : Pack n → I) (j : ℕ) := let p := Pack.ofAddress P.activities j
    if j=slot hP p then F p else 0

lemma selects {I : Type*} [Zero I] (F : Pack n → I) (i : Pack n) : allocate hP F (slot hP i)= F i := by
  unfold allocate; rw [address]; simp

lemma wrapped (F : Pack n → Config G n → ℂ) {X : Support n}
    (h : ∀ i, Legible P.p i (F i) ∧ (F i ≠ 0 → X ⊆ i.zone)) (i : ℕ) :
    let A := allocate hP F i; let k := P.activities.forced i
    GaugeInvariant A ∧ UsesFinal P.p.threshold k.support A ∧ Measurable A ∧ (A ≠ 0 → X ⊆ k.support) ∧
      ∀ U,A U ≠ 0 → k.eligible P.p.threshold U := by
  unfold allocate; simp only
  split
  · rename_i he; let q := Pack.ofAddress P.activities i
    have hh i := (h i).1
    refine ⟨(hh _).symmetry,(hh q).reads,(hh _).borel,(h q).2,fun U hu => ?_⟩
    have hl := (hh _).inventory U hu
    change _ ∧ _
    exact ⟨hl,he ▸ check hP q U hl⟩
  exact ⟨fun _ _ => rfl,fun _ _ _ _ => rfl,measurable_const,fun h => False.elim (h rfl),fun _ h => False.elim (h rfl)⟩

lemma allocation (F : Pack n → Config G n → ℂ) (U : Config G n) (i : Pack n) :
    Pack.collect P (fun j => allocate hP F j U) i=F i U := by
  unfold Pack.collect
  rw [tsum_eq_single (slot hP i),address]
  · simp only [if_true]; exact congr_fun (selects hP F i) U
  intro j hj
  unfold allocate; split
  · rename_i he; dsimp only
    rw [if_neg (show j ≠ _ from he.symm ▸ hj)]; rfl
  rfl

lemma expenses {r c : ℝ} (F : Pack n → Config G n → ℂ) (h : ∃ A : Pack n → ℝ,
    (∑ i,burn P.p r i.zone*A i) ≤ c ∧ ∀ i,0 ≤ A i ∧ ∀ U, ‖F i U‖ ≤ A i) :
    ∃ f : ℕ → ℝ, SumBudget (fun i => burn P.p r (P.activities.forced i).support*f i) c ∧
       ∀ i,0 ≤ f i ∧ ∀ U, ‖allocate hP F i U‖ ≤ f i := by
  obtain ⟨A,hA,hf⟩ := h
  let f := allocate hP A
  let g i := burn P.p r (P.activities.forced i).support*f i
  let S := univ.image (slot hP)
  have hg i : 0 ≤ f i ∧ ∀ U,‖allocate hP F i U‖ ≤ f i := by
    unfold f allocate; simp only; split_ifs
    · exact hf _
    exact ⟨le_rfl,fun U => norm_zero.le⟩
  have he i (hi : i∉S) : g i=0 := by
    unfold g f allocate; simp only; split
    · rename_i hj; exact False.elim (hi (Finset.mem_image.mpr ⟨_,mem_univ _,hj.symm⟩))
    exact mul_zero _
  refine ⟨f,⟨fun i => mul_nonneg (burn_pos ..).le (hg i).1,?_,?_⟩,hg⟩
  · exact summable_of_ne_finset_zero he
  rw [tsum_eq_sum he,Finset.sum_image (check_inj hP).injOn]
  have hv i : g (slot hP i) = burn P.p r i.zone*A i := by
    unfold g f; rw [selects, ← congrArg Pack.zone (address hP i)]; rfl
  change (∑ i, g (slot hP i)) ≤ _; simp_rw [hv]; exact hA
end YM.AnalyticNext.GridStop.Primary
