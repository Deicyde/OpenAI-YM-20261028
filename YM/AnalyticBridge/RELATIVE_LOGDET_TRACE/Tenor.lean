import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Currencies
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Reading
import YM.Next.EXTRACTION.Mixture

/-!
# Finite reads of the window **letters**, not of log A itself

Use e.g. with Z=inventory or larger. `ReadTogether` for a generic pair
includes actual aperture checks on both sides; no positivity needed since
checking equalities even of the total expressions on ambient fields. This
also handles changing some of the windows (but not pretending that gives
the same density as if the covariance hadn't changed!).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Function Set Matrix MeasureTheory Lattice RG Wilson Pressure Tree
open Next.SectorChange Next.Fluctuations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

section patch
variable {ι : Type} [Fintype ι] [DecidableEq ι] {c : Side} {B : ℕ} {p : ι → Site c} {Z : Support c} {A A' : Square ι}
  {W W' : ι → Set ι}

structure ReadTogether (p : ι → Site c) (Z : Support c) (B : ℕ) (W W' : ι → Set ι) (A A' : Square ι) : Prop where
  pipe : Aperture p B W A
  pipe' : Aperture p B W' A'
  self : ∀ i, i∈W i
  kernel : ∀ i : ι, Shields Z (p i) (14*B) → ∀ j : ι,A i j=A' i j
  windows : ∀ i : ι, Shields Z (p i) (14*B) → W i=W' i

namespace ReadTogether
variable (h : ReadTogether p Z B W W' A A') {l : ℕ}
include h

lemma column (i : ι) (H : Shields Z (p i) (15*B)) (u : ℝ) (j : ι) : pie W A u j i=pie W' A' u j i := by
  have he := h.windows i (H.shrink (by omega))
  have hp := h.self i
  have hs x (hx : x∈W i) : Shields Z (p x) (14*B) := H.shift (by have ht : separation (p i) (p x) ≤ B/2 := h.pipe.2 i x hx; omega)
  by_cases hy : j∈W i
  · have hz : Schur.principal A (W i)=Schur.principal A' (W i) := by
      ext k y; exact h.kernel _ (hs k k.property) y.val
    rw [pie_read W _ u j i hy hp,pie_read W' _ u j i (he ▸ hy) (he ▸ hp),hz]
    have hr (s t : Set ι) (H : s=t) (hj : j∈s) (hx : i∈s) :
        FreeResolvent.resolve (Schur.principal A' s) u ⟨j,hj⟩ ⟨i,hx⟩ =
        FreeResolvent.resolve (Schur.principal A' t) u ⟨j,H ▸ hj⟩ ⟨i,H ▸ hx⟩ := by subst t; rfl
    exact hr _ _ he hy hp
  rw [pie_miss W _ _ _ _ hy,pie_miss W' _ _ _ _ (he ▸ hy)]

lemma row (i : ι) (H : Shields Z (p i) (16*B)) (u : ℝ) (j : ι) : pie W A u i j=pie W' A' u i j := by
  by_cases hp : nearby p (B/2) i j
  · exact h.column j (H.shift (by unfold nearby at hp; omega)) u i
  rw [h.pipe.glance u i j hp,h.pipe'.glance u i j hp]

lemma fog_column (i : ι) (H : Shields Z (p i) (16*B)) (j : ι) : Schur.clouded W A j i=Schur.clouded W' A' j i := by
  rw [sym_cloud,sym_cloud]
  simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,h.column i (H.shrink (by omega)), h.row i H]

lemma obstruction (i : ι) (H : Shields Z (p i) (17*B)) (j : ι) (u : ℝ) : defect W A u i j=defect W' A' u i j := by
  by_cases hm : nearby p B i j
  · unfold defect
    simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.add_apply]
    refine congr_arg (· - _) (Finset.sum_congr rfl fun k _ => ?_)
    rw [h.kernel i (H.shrink (by omega)), h.column j (H.shift (by unfold nearby at hm; omega))]
  rw [h.pipe.light u i j hm,h.pipe'.light u i j hm]

lemma correction (i : ι) (H : Shields Z (p i) (17*B)) (j : ι) : excess W A i j=excess W' A' i j := by
  by_cases hm : nearby p B i j
  · simp only [excess, Matrix.sub_apply,Matrix.mul_apply]
    refine congr_arg (· - _) (Finset.sum_congr rfl fun k _ => ?_)
    rw [h.kernel i (H.shrink (by omega)), h.fog_column j (H.shift (by unfold nearby at hm; omega))]
  rw [h.pipe.spare i j hm,h.pipe'.spare i j hm]

lemma local_value (hl : 15≤l) (i : ι) (H : lens p l B i⊆Z) : letterBase W A i=letterBase W' A' i := by
  unfold letterBase; simp_rw [h.column i ((Shields.full p i l B H).shrink (by gcongr))]

lemma manuscript (hl : 17 ≤ l) (z : Letter ι 1) (he : inventory p l B z ⊆ Z) :
    scroll W A z.2.1 z.2.2=scroll W' A' z.2.1 z.2.2 := by
  let i:=z.2.1; let x:=z.2.2
  funext u
  by_cases ht : jumps (nearby p B) i i x
  · change -(road _ _ _ _ x) = -(road _ _ _ _ _)
    exact congr_arg (-(·)) (pocket_through p Z x he ht
      (fun i j hi _ => h.row i ((Shields.full p i l B hi).shrink (Nat.mul_le_mul_right _ (by omega : 16 ≤ l))) u j)
      (fun i j hi _ => congr_arg (-(·)) (h.obstruction i ((Shields.full p i l B hi).shrink (Nat.mul_le_mul_right _ hl)) j u)))
  rw [h.pipe.away z ht, h.pipe'.away z ht]

lemma notices (hl : 17≤l) (z : Letter ι 0) (he : inventory p l B z ⊆ Z) : errata W A z=errata W' A' z := by
  let i:=z.2.1; let x:=z.2.2
  by_cases hp : jumps (nearby p B) i i x
  · have ht (i j : ι) (hs : lens p l B i⊆Z) (hm : nearby p B i j) : (-excess W A) i j=(-excess W' A') i j := congr_arg
      (-(·)) (h.correction i ((Shields.full p i l B hs).shrink (Nat.mul_le_mul_right _ hl)) j)
    exact congr_arg (fun m : ℝ => -m/((z.1:ℝ)+1)) (pocket_through p Z x he hp ht ht)
  rw [h.pipe.quiet z hp,h.pipe'.quiet z hp]
end ReadTogether
end patch

namespace Physical
variable {G : Gauge} {c f : Side} {x : ℝ} {S : StepData c f} {F H : Forest S.ratio} {A A' : Stores S} {V V' : Config G c} {k k' : S.Choices}
  (T : Tube G S)

lemma aligned {Z : Support c} (h : Reads Z A A' F H V V' k k') (hS : S.patch.Branches S.kernel G) (hB : 120 ≤ radiusB x)
    (hl : Next.SectorChange.span S.patch x ≤ radiusB x/50) :
    ReadTogether (place S) Z (radiusB x) (windows S x) (windows S x) (AFull T A F x V k) (AFull T A' H x V' k') where
  pipe := furnished T k V hS A F hl
  pipe' := furnished T k' V' hS A' H hl
  self := centered hB
  kernel i := h.same_row hS T i hB hl
  windows _ _ := rfl


end Physical
end YM.AnalyticBridge.RelativeLogdet
