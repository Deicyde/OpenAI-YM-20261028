import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Merge

set_option warningAsError false

/-!
# The two exact exclusions caused by extracting an unforced action

* its unrestricted exponential expands polymers that may touch forced
  supports
* its contribution to v (if nonzero) is extensive, not masked.

Correct both IN THE DENSITY. If a log-cluster footprint is healthy,
its omission costs minus the actual signed value there. If not, all
its term values used in the log already vanish, but it needs MINUS its
extracted scalar upon attachment. These alternatives can be the SAME
restoration address (zero or one of the two numerical charges), with
the same weights for convergence. Both need to be enumerated only when
incident to an original d. Keep the final flag read.

Like E, absorb only the log-constant contribution
here; other extensive scalars from step kernel, changing coordinates,
base etc stay external.

Result concerns equality of densities; other
parts of activity receipts (bounds, reference affine jets, symmetry,
etc) separate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Restore
open Lattice RG Wilson AbsoluteSums Ursell Finset Filter Function Attach
open scoped Topology Classical BigOperators
variable {n : Side} {ι κ : Type*} (X : ι → Support n) (Y I : κ → Support n)
    (D : Support n) (u : ι → ℝ) (d : κ → ℝ)

def good (i : ι) : ℝ := if Disjoint (X i) D then u i else 0

lemma good_norm (i : ι) {b : ι → ℝ} (h : ∀ i,0≤b i) (he : Disjoint (X i) D → ‖u i‖ ≤ b i) :
    ‖good X D u i‖ ≤ b i := by
  unfold good; split
  next hh => exact he hh
  rw [norm_zero]; exact h _

def Z (i : Clusters ι) := unionOf X i.2

def raw (i : Clusters ι) := Gas.term (blocked X) u i

lemma Zcontains (i : Clusters ι) (k) : X (i.2 k) ⊆ Z X i :=
  fun _ h => mem_biUnion.mpr ⟨k,mem_univ _,h⟩

lemma Znonempty (hX : ∀ i,(X i).Nonempty) (i : Clusters ι) : (Z X i).Nonempty :=
  (hX (i.2 none)).mono (Zcontains X i _)

lemma masked_term (i : Clusters ι) :
    Gas.term (blocked X) (good X D u) i = good (Z X) D (raw X u) i := by
  unfold good; split
  next h =>
    unfold Gas.term raw; congr 2
    apply prod_congr rfl; intro j _
    exact if_pos (Finset.disjoint_left.mpr fun x hx he => Finset.disjoint_left.mp h (Zcontains X i _ hx) he)
  next h =>
    have he := (not_disjoint_iff.mp h)
    obtain ⟨x,hX,hD⟩ := he
    obtain ⟨k,hk,hx⟩ := mem_biUnion.mp hX
    unfold Gas.term
    rw [prod_eq_zero (f:=fun k => (if Disjoint (X (i.2 k)) D then u (i.2 k) else 0)) hk (show (if Disjoint (X (i.2 k)) D then u (i.2 k) else 0) = 0 from if_neg (Finset.not_disjoint_iff.mpr ⟨x,hx,hD⟩)),mul_zero,zero_div]

section Scalar
variable (v : Clusters ι → ℝ)

/-- Log contributions to the additive term with the convention of
`Rep.exponent` (`-additive` there). v is the log value removed from
each cluster (typically raw at identity, NOT the input scalar).
-/
def regular (i : Clusters ι) := -(raw X u i) + v i

/-- One restoration address suffices for both corrections. Keep the
same label & complete footprint regardless of branch. -/
def takeBack (i : Clusters ι) :=
  if Disjoint (Z X i) D then -(raw X u i) else -v i

private def scalarBad (i : Clusters ι) := if Disjoint (Z X i) D then 0 else v i



private lemma forces_reach (A : Finset κ) (i : Clusters ι) (hI : ∀ j,I j ⊆ Y j)
    (h : Records Y I D A) (he : ¬ Disjoint (Z X i) D) : reaches Y (Z X) A i := by
  obtain ⟨x,hx,hD⟩ := Finset.not_disjoint_iff.mp he
  rw [← h.2] at hD
  obtain ⟨j,hj,hi⟩ := mem_biUnion.mp hD
  exact Finset.not_disjoint_iff.mpr ⟨x,mem_biUnion.mpr ⟨j,hj,hI j hi⟩,hx⟩

lemma entry_terms (hI : ∀ j,I j⊆Y j) (A : Finset κ) (h : Records Y I D A) (i : Clusters ι) :
    entry Y (Z X) (takeBack X D u v) A i =
      -(Gas.missing X (A.biUnion Y) (good X D u) i) - scalarBad X D v i := by
  unfold entry takeBack Gas.missing scalarBad
  rw [← Z]
  by_cases he : Disjoint (Z X i) D
  · by_cases hl : Disjoint (A.biUnion Y) (Z X i)
    · simp [hl,he,reaches]
    simp [hl,he,reaches,masked_term,good]
  have ht := forces_reach X Y I D A i hI h he
  rw [if_pos ht,if_neg he,if_neg ht,if_neg he, masked_term,good,if_neg he]; ring

lemma takeBack_summable (hv : Summable fun i => ‖v i‖)
    (h : Summable fun i => ‖Gas.term (blocked X) (good X D u) i‖) :
    Summable fun i => ‖takeBack X D u v i‖ := by
  apply (h.add hv).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  rw [masked_term]; unfold takeBack good; split
  · rw [norm_neg]; exact le_add_of_nonneg_right (norm_nonneg _)
  rw [norm_neg]; exact le_add_of_nonneg_left (norm_nonneg _)



private lemma tally_b (hv : Summable fun i => ‖v i‖) : Summable fun i => ‖scalarBad X D v i‖ := by
  apply hv.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i; unfold scalarBad; split
  · exact norm_zero.trans_le (norm_nonneg _)
  exact le_rfl

lemma regular_abs (h : Summable fun i => ‖Gas.term (blocked X) (good X D u) i‖) (hv : Summable fun i => ‖v i‖) :
    Summable fun i => ‖good (Z X) D (regular X u v) i‖ := by
  apply (h.add hv).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  rw [masked_term]; unfold regular good; split
  · exact (norm_add_le ..).trans (by rw [norm_neg])
  exact le_add_of_nonneg_right (norm_nonneg _)

lemma scalar_bill (h : Summable fun i => ‖Gas.term (blocked X) (good X D u) i‖) (hv : Summable fun i => ‖v i‖) :
    (∑' i,v i) - (∑' i,good (Z X) D (regular X u v) i) =
      Gas.logSum (blocked X) (good X D u) + ∑' i,scalarBad X D v i := by
  unfold Gas.logSum
  rw [← hv.of_norm.tsum_sub (regular_abs X D u v h hv).of_norm,
    ← h.of_norm.tsum_add (tally_b X D v hv).of_norm]
  apply tsum_congr; intro i; rw [masked_term]; unfold regular good scalarBad; split <;> ring

/-- Reconnected output gas index. For incidence and for merge here use
precisely the actual complete footprints. -/
abbrev Out := Species' Y (Z X)

def K (i : Out X Y) := merged Y Y I (Z X) (Z X) D d (takeBack X D u v) i
abbrev location := zone Y (Z X)
abbrev flagsOut := hold Y I (Z X)

/-- The exact finite-volume identity on real activities with complete
masks and restored K addresses. v can be any further absolutely
summable family of log values extracted to the scalar (incl zeros).
Thus can apply *before* a normalization choice. Y is the full forced
support (for all its compat checks at this merger).
-/
theorem output_eq (hX : ∀ i,(X i).Nonempty) (hY : ∀ i,(Y i).Nonempty) (hI : ∀ i,I i ⊆ Y i)
    (B : ℕ) {a γ δ q : ℝ} (ha : 0 ≤ a) (h : Trees.Ready X B (fun i => ‖good X D u i‖) a γ δ q)
    (hd : Summable fun i => ‖d i‖) (hv : Summable fun i => ‖v i‖) :
    let full := gasTerm (both Y X) (onlyL I) D (Sum.elim d (good X D u))
    let addi := good (Z X) D (regular X u v)
    let out := gasTerm (location X Y) (flagsOut X Y I) D (K X Y I D u d v)
    Summable (fun i => ‖full i‖) ∧ Summable (fun i => ‖addi i‖) ∧ Summable (fun i => ‖out i‖) ∧
    (∑' i,full i) = Real.exp ((∑' i,v i) - (∑' i,addi i)) * ∑' i,out i := by
  have he := exclusion X Y I D (good X D u) d hd hX B ha h
  obtain ⟨he,ht,hm,hs,hf⟩ := he
  have hh := takeBack_summable X D u v hv ht
  have hx := Attach.merge Y Y I (Z X) (Z X) D d (takeBack X D u v) (fun _ => Finset.Subset.refl _) (fun _ => Finset.Subset.refl _) hI
    (Znonempty X hX) hY hd hh
  intro full addi out
  refine ⟨he,regular_abs X D u v ht hv,hx.1,hf.trans ?_⟩
  let c := ∑' i,scalarBad X D v i
  have hg (A : Finset κ) : residual X Y I D (good X D u) d A =
      Real.exp c * paid Y I (Z X) D d (takeBack X D u v) A := by
    by_cases hl : Records Y I D A
    · have hc : (∑' i,entry Y (Z X) (takeBack X D u v) A i) =
          -(omission X Y (good X D u) A) - c := by
        unfold omission c
        rw [← tsum_neg, ← (hm A).of_norm.neg.tsum_sub (tally_b X D v hv).of_norm]; apply tsum_congr
        exact entry_terms X Y I D u v hI A hl
      unfold residual paid; rw [hc,mul_left_comm,← Real.exp_add,  show c + (-omission X Y (good X D u) A - c) = -omission X Y (good X D u) A by ring]
    simp [residual,paid,gasTerm,hl]
  have hr : Real.exp (Gas.logSum (blocked X) (good X D u)) * Real.exp c =
      Real.exp ((∑' i,v i) - (∑' i,addi i)) := by
    rw [← Real.exp_add,scalar_bill X D u v ht hv]
  have hE : (∑' A,residual X Y I D (good X D u) d A)=Real.exp c * ∑' i,out i := by
    simp_rw [hg]; exact (tsum_mul_left).trans (congr_arg _ hx.2)
  rw [hE,← mul_assoc,hr]
end Scalar
end YM.Push.LogIdentity.Restore
