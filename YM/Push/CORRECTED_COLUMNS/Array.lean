import YM.Push.CORRECTED_COLUMNS.Polynomial

/-!
# Global source polynomial coefficients

Census all. One global array, unnormalized. Different slots even for
copies using the same label. Replicating this way from the initial cell
also transports *scalar coefficients* at the proper hands.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Marks
open Lattice Cells Wilson MeasureTheory Marker
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {V : Type*} [DecidableEq V] [Fintype V]

section
variable {I : Type*} [DecidableEq I] [Fintype I]

def fibre (p : Finset (I × V)) (i : I) := Finset.univ.filter (fun j : V => (i,j)∈p)

def located (p : Finset (I × V)) (l : Finset I) := ∀ q∈p,q.1∈l
instance (p : Finset (I × V)) (l : Finset I) : Decidable (located p l) := by unfold located; infer_instance

def into (F : Algebra V) (i : I) : Algebra (I × V) := Poly.inject fun x => if located x.val {i} then part F (fibre x.val i) else 0
lemma belongs (F : Algebra V) (i : I) (p : Finset (I×V)) :
    part (into F i) p = if located p {i} then part F (fibre p i) else 0 := rfl

/-- Exact square-zero replication. Not specializing to a particular max degree. -/
lemma spread (l : Finset I) (F : I → Algebra V) (p : Finset (I×V)) :
    part (∏ i∈l, into (F i) i) p = if located p l then ∏ i∈l, part (F i) (fibre p i) else 0 := by
  induction l using Finset.induction_on generalizing p with
  | empty =>
    rw [Finset.prod_empty]; unfold part; rw [Poly.one_part]
    have he : located p ∅ ↔ p=∅ := by simp [located, Finset.eq_empty_iff_forall_notMem]
    rw [← mode_empty]
    simp only [he,mode_inj,Finset.prod_empty]
  | @insert i s hi ih =>
  rw [Finset.prod_insert hi,convolution]
  simp_rw [belongs,ih]
  let a := p.filter fun x => x.1=i
  have ha : a∈p.powerset := Finset.mem_powerset.mpr (Finset.filter_subset ..)
  have hv : located a {i} := fun j hj => Finset.mem_singleton.mpr (Finset.mem_filter.mp hj).2
  have hx (q) (h : q∈p.powerset) (hf : located q {i}) (he : located (p \ q) s) : q=a := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mp h hx, Finset.mem_singleton.mp (hf _ hx)⟩
    intro hy; by_contra w
    obtain ⟨hw,hy⟩ := Finset.mem_filter.mp hy
    exact hi (hy ▸ he _ (Finset.mem_sdiff.mpr ⟨hw,w⟩))
  by_cases hu : located p (insert i s)
  · have he : located (p \ a) s := by
      intro q hq; obtain ⟨hg,hq⟩ := Finset.mem_sdiff.mp hq
      exact (Finset.mem_insert.mp (hu _ hg)).resolve_left fun w => hq (Finset.mem_filter.mpr ⟨hg,w⟩)
    rw [if_pos hu,Finset.prod_insert hi,Finset.sum_eq_single a,if_pos hv,if_pos he]
    · rw [show fibre a i=fibre p i by ext; simp [a,fibre]]
      congr 1; refine Finset.prod_congr rfl fun j hj => ?_
      have hh : j≠i := by rintro rfl; exact hi hj
      rw [show fibre (p \ a) j=fibre p j by ext; simp [a,fibre,hh]]
    · intro b hb h
      split_ifs with h' h' h'
      · exact (h (hx _ hb ‹located b _› ‹located _ s›)).elim
      all_goals simp
    exact fun w => (w ha).elim
  rw [if_neg hu]
  apply Finset.sum_eq_zero; intro x h
  split_ifs with e e' e'
  · exfalso; apply hu
    intro q hq
    by_cases hg : q∈x
    · rw [Finset.mem_singleton.mp (e q hg)]; simp
    exact Finset.mem_insert_of_mem (e' _ (Finset.mem_sdiff.mpr ⟨hq,hg⟩))
  all_goals simp

lemma copied (F : I → Algebra V) (p : Finset (I × V)) :
    part (∏ i, into (F i) i) p = ∏ i, part (F i) (fibre p i) := by
  rw [spread,if_pos (show located p Finset.univ from fun x _ => Finset.mem_univ _)]
end

section
variable {n : Side} {G : Gauge} (T : Tiling n)

-- Conjugate the coefficients when hand requires it; not its own choice for each atom or new calls on calibration.
def replicate (P : Config G n → Algebra V) (U : Config G n) : Algebra (T.Cell × V) :=
    ∏ i : T.Cell, into (Poly.inject (R:=all V) fun z => T.copy i (fun X => (P X).part z) U) i

lemma divides (P : Config G n → Algebra V) (p : Finset (T.Cell × V)) (U) :
    part (replicate T P U) p=∏ i, T.copy i (fun X => part (P X) (fibre p i)) U := copied ..

lemma unchanged (P : Config G n → Algebra V) (h : ∀ U, part (P U) ∅=1) U :
    part (replicate T P U) ∅=1 := by
  rw [divides]; apply Finset.prod_eq_one; intro i _; unfold Tiling.copy; split <;> simp [fibre,h]

/-- Constant u in each cell. -/
def packed (u : Finset V) : Finset (T.Cell × V) := Finset.univ ×ˢ u

lemma folded (P : Config G n → Algebra V) (u : Finset V) (U) :
    part (replicate T P U) (packed T u)=∏ i, T.copy i (fun X => part (P X) u) U := by
  have he i : fibre (packed T u) i = u := by ext; simp [fibre,packed]
  rw [divides]; simp_rw [he]

lemma continuous_array (P : Config G n → Algebra V) (h : ∀ s, Continuous fun U => part (P U) s) (z : Finset (T.Cell × V)) :
    Continuous fun U => part (replicate T P U) z := by
  simp_rw [divides]
  refine continuous_finsetProd _ (fun i _ => ?_)
  unfold Tiling.copy; split
  · exact continuous_star.comp ((h _).comp (continuous_pull _ _))
  exact (h _).comp (continuous_pull _ _)
end
end YM.Push.Corrected.Marks
