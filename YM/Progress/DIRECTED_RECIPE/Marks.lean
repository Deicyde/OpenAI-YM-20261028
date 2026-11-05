import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.IntegralConvolution
import YM.Extraction.Orders
import YM.Overlay.Table
import YM.Progress.DIRECTED_RECIPE.Padding
import YM.Source.Insertion
import YM.TimeKernel.Trace



/-!
# Downstream applicability of this dictionary

Hold `P : Rep` and its vacuum receipts. If attaching in an augmented
vocabulary, transport the **actual marked** sums to P without selecting a
new vacuum. Bounds as well as exact identities. Embeddings once fixed,
same placement, including all choice footprints. `OverlayMap` is a sufficiency
alignment test; for using on a real Fit with its available slots use
`annexed` when those augmentation hypotheses are supplied. Does not deal
with organizing integrations for new histories (need prove they deliver
actual aligned ancestors); no claim e.g. marker expressions at shifted
ancestors are then available without proof.

The sum-equality lemmas apply also to bare `tsum`, but clients need the
Budget and Format/Bands receipts earlier than concluding any true evaluation!
The embeddings are chosen ONCE, incl for linear coefficient
families.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe
open Function Set RG Wilson Lattice Source MeasureTheory Overlay Marker
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

/-- Align *representatives*, don't commute tags by just equality of
vacuum expectations. -/
structure OverlayMap (e k : ℕ ↪ ℕ) (A B : Rep G n) : Prop where
  value : B.v=A.v
  epoch : B.beta=A.beta
  paths : B.path=A.path
  point : B.p=A.p
  clip : B.clip=A.clip
  index : Readdress A.p e k A.activities B.activities



namespace OverlayMap
variable {A B : Rep G n} {e k : ℕ ↪ ℕ} (h : OverlayMap e k A B)
include h


omit h

/-! Singles -/
section Singles
variable {d : ℕ} {F : Labels.Frame G d} (p : Coefficient F n)

def relay (k : ℕ ↪ ℕ) (p : Coefficient F n) : Coefficient F n := { p with forced := stuff k p.forced }

lemma linear {w : F.Coeff → Coefficient F n} (H : IsLinearMap ℂ fun x => (w x).forced)
    (k : ℕ ↪ ℕ) : IsLinearMap ℂ fun x => (relay k (w x)).forced := by
  constructor
  · intro x y; funext i U
    by_cases hi : i ∈ range k
    · obtain ⟨j,rfl⟩ := hi
      simp only [relay,stuffed,Pi.add_apply]
      exact congr_fun (congr_fun (H.map_add x y) j) U
    simp only [relay,blank _ _ hi, Pi.add_apply, Pi.zero_apply, add_zero]
  intro c x; funext i U
  by_cases hi : i ∈ range k
  · obtain ⟨j,rfl⟩ := hi
    simp only [relay,stuffed,Pi.smul_apply]; exact congr_fun (congr_fun (H.map_smul _ _) _) _
  simp only [relay,blank _ _ hi,Pi.smul_apply,Pi.zero_apply,smul_zero]

include h





end Singles

section Many
variable {V : Type*} [Fintype V] [DecidableEq V] {R : Census V} (v : Bands R A)

/-- At off-range addresses pad secondary slots with existing Mode metadata
(which then has the required Nonempty under Active), NO semantic coefficient
or placement changes. -/
def issue (k : ℕ ↪ ℕ) (v : Bands R A) (B : Rep G n) : Bands R B where
  origins := v.origins
  units := v.units
  support := v.support
  rays := v.rays
  H := v.H
  marks := extend k v.marks (fun _ => v.marks 0)
  entries := stuff k v.entries

include h
omit [Fintype V] in
lemma active (hh : v.Active) : (issue k v B).Active := by
  refine ⟨hh.proper,hh.pins,fun i => ?_,?_,?_,?_,?_,?_,?_⟩
  · rw [h.point]; exact hh.regular i
  · intro i j; unfold issue
    by_cases hi : i∈range k
    · obtain ⟨i,rfl⟩ := hi; simp only [k.injective.extend_apply]; exact hh.occurs i j
    simp only [extend_apply' _ _ _ (show ¬ ∃ a,k a=i from hi)]; exact hh.occurs 0 j
  · intro i j
    by_cases hi : i∈range k
    · obtain ⟨i,rfl⟩ := hi; simp only [issue,stuffed,k.injective.extend_apply,h.index.sup]; exact hh.retained i j
    simp only [issue,blank _ _ hi,Pi.zero_apply,ne_eq,not_true_eq_false,false_implies]
  · intro i j
    by_cases hi : i∈range k
    · obtain ⟨i,rfl⟩ := hi; simp only [issue,stuffed,h.index.sup,h.point]; exact hh.inspects i j
    simp only [issue,blank _ _ hi,Pi.zero_apply]; exact fun _ _ _ _ => rfl
  · intro i j U; by_cases hi : i∈range k
    · obtain ⟨i,rfl⟩ := hi; simp only [issue,stuffed,h.point]
      exact fun hv => h.index.admits i U (hh.keeps _ _ U hv)
    simp only [issue,blank _ _ hi,Pi.zero_apply,ne_eq,not_true_eq_false,false_implies]
  · intro i j; by_cases hi : i∈range k
    · obtain ⟨i,rfl⟩ := hi; simp only [issue,stuffed]; exact hh.meas i j
    simp only [issue,blank _ _ hi,Pi.zero_apply]; exact measurable_const
  intro i j; by_cases hi : i∈range k
  · obtain ⟨i,rfl⟩ := hi; simp only [issue,stuffed]; exact hh.invi i j
  simp only [issue,blank _ _ hi,Pi.zero_apply]; exact fun _ _ => rfl

omit [Fintype V] in
lemma radial {w : V → ℝ} {u c d b : ℝ} (hh : v.Radial w u c d b) :
    (issue k v B).Radial w u c d b := by
  obtain ⟨hf,hv,ha,hb,t, ht,H⟩ := hh
  refine ⟨hf,hv,ha,?_,?_⟩
  · rw [h.point]; exact hb
  let K := k.prodMap (Function.Embedding.refl ℕ)
  have he (i j) : (i,j)∈range K ↔ i∈range k := by
    constructor
    · rintro ⟨⟨i',j'⟩,he⟩; exact ⟨i',congr_arg Prod.fst he⟩
    rintro ⟨i,rfl⟩; exact ⟨(i,j),rfl⟩
  refine ⟨stuff K t, fun i j => ?_, fun i => transfer_budget K ?_ ?_ (H i)⟩
  · by_cases hi : i∈range k
    · obtain ⟨i,rfl⟩ := hi; rw [show (k i,j)=K (i,j) from rfl,stuffed]
      simp only [issue,stuffed]; exact ht i j
    simp only [issue,blank _ _ hi,blank _ _ (mt (he i j).1 hi),Pi.zero_apply,norm_zero,le_refl,
      implies_true,true_and]
  · rintro ⟨i',j'⟩
    simp only [stuffed,issue,h.point]
    simp only [show K (i',j')=(k i',j') from rfl,h.index.sup,
      k.injective.extend_apply]
  rintro ⟨i',j'⟩ hj
  simp [blank _ _ hj, BudgetPoint.mass]


end Many
end OverlayMap
end YM.Progress.DirectedRecipe
