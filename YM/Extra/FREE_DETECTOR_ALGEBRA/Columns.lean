import YM.Extra.FREE_DETECTOR_ALGEBRA.Rank


set_option warningAsError false

/-!
# Concrete finite point scanners / Columns

Parameter F fixes all bases before comparison. Pair set works for **any**
single choice of pair separation; use a generic one for compatibility with
layout. Contains weight-zero unit and all indicated partners from the same
constrained gauge-invariant sector. RCorrected must still fit grids, lifts
and replication estimates. This file gives NO lower bound of interacting
system nor a Trial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder Matrix

variable {G : Gauge} (F : Labels.Frames G)
local notation "T" => freeTable F
local notation "W" => Table.Field (freeTable F)

/-- Images of the *same reference frame* suffice. -/
def sourceAt (d : ℕ) : Label G d →ₗ[ℂ] W d := ((freeTable F).project d).comp (F.level d).coords.toLinearMap

lemma labeled (d : ℕ) : ∃ (n : ℕ) (b : Module.Basis (Fin (n+1)) ℂ (W d)), b 0=(freeTable F).unit d ∧
    ∀ i : Fin (n+1), ∃ j, b i=sourceAt F d ((F.level d).basis j) := by
  classical
  let U := F.level d
  let S := range (fun i => sourceAt F d (U.basis i))
  let v := (freeTable F).unit d
  have hv : v ≠ 0 := (freeTable F).alive d (table_regular F)
  have ht : v ∈ S := by
    refine ⟨0,?_⟩
    apply writes_inj F d
    rw [show writes F d v = 1 from writes_unit F d]
    change writes F d ((freeTable F).project _ (U.coords (U.basis 0)))= _
    rw [U.starts_unit,writes_project]
    change observable G d (U.coords.symm (U.coords _))=_
    rw [LinearEquiv.symm_apply_apply]; exact map_one reduceEq
  have he : ⊤ ≤ Submodule.span ℂ S := by
    intro i _
    obtain ⟨p,rfl⟩ := (freeTable F).onto d i
    obtain ⟨p,rfl⟩ := U.coords.surjective p
    change sourceAt F d p ∈ _
    rw [← U.basis.sum_repr p,_root_.map_sum]
    exact Submodule.sum_mem _ fun j _ => by
      rw [_root_.map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
  have hi : LinearIndepOn ℂ id ({v}:Set (W d)) := (linearIndepOn_singleton_iff ℂ).mpr hv
  obtain ⟨s,hs,hu,hh,hy⟩ := exists_linearIndepOn_id_extension
    hi (Set.singleton_subset_iff.mpr ht)
  let b : Module.Basis s ℂ (W d) := Module.Basis.mk (show LinearIndependent ℂ (Subtype.val : s → _) from hy.linearIndependent_restrict)
      (by simpa using le_trans he (Submodule.span_le.mpr hh))
  haveI := Module.Finite.finite_basis b
  letI := Fintype.ofFinite s
  let i : s := ⟨v,hu (by simp)⟩
  have hp : Nonempty s := ⟨i⟩
  let n := Fintype.card s - 1
  have he : Fintype.card s=n+1 := by have := Fintype.card_pos_iff.mpr hp; dsimp [n]; omega
  let f := (Fintype.equivFin s).trans (finCongr he)
  let g := f.trans (Equiv.swap (f i) 0)
  have hj (i : s) : b.reindex g (g i) = i.val := by simp [b]
  refine ⟨n,b.reindex g, (by rw [← show g i = 0 by simp [g],hj]), fun i => ?_⟩
  obtain ⟨i,rfl⟩ := g.surjective i
  obtain ⟨j,hj'⟩ := hs i.property
  exact ⟨j,(hj i).trans hj'.symm⟩

lemma frameRows (d : ℕ) (h : (freeTable F).RealSpin) : ∃ (n : ℕ) (b : Module.Basis (Fin (n+1)) ℂ (W d)),
    b 0=(freeTable F).unit d ∧ (∀ i, (freeTable F).conj h d (b i)=b i) ∧ ∀ i, ∃ j, b i=sourceAt F d ((F.level d).basis j) := by
  obtain ⟨n,b,hb,hw⟩ := labeled F d
  refine ⟨n,b,hb,fun i => ?_,hw⟩
  obtain ⟨j,hj⟩ := hw i
  apply writes_inj F d
  rw [writes_bar, hj]
  let U := F.level d
  have he : writes F d (sourceAt F d (U.basis j))= observable G d (U.basis j) := by
    rw [sourceAt,LinearMap.comp_apply,writes_project]; change observable G d (U.coords.symm (U.coords _))= _
    rw [LinearEquiv.symm_apply_apply]
  change barPol (writes F d (sourceAt F d (U.basis j))) = _
  rw [he,← observe_bar,U.realForm]

/-- Raw scanner entry at a separated pair. -/
def readsTwo (d : ℕ) (x y : E4) := LinearMap.BilinForm.comp (joinLin x y) (writes F d) (writes F d)

lemma scan_used (d : ℕ) (x y : E4) (P Q : W d) : readsTwo F d x y P Q =
    (freeTable F).useAt T (couple x y) ![⟨d,P⟩,⟨d,Q⟩] := by
  rw [writes_eval]; change joinLin x y _ _ = moment G _ _
  rw [joinLin_apply]; unfold join; congr 1; ext1 i; fin_cases i <;> rfl

/-- All-index reflection at y; includes *ordinary* conjugation. -/
def faceTest (d : ℕ) (x y : E4) (Q : W d) : W d := ride F (face (x-y)) d ((freeTable F).conj (table_spin F) d Q)

theorem faceTest_eq (d : ℕ) (x y : E4) (P Q : W d) :
    readsTwo F d x y P (faceTest F d x y Q) = duplex x y (writes F d P) (writes F d Q) := by
  unfold faceTest; change joinLin x y _ _ = _
  rw [ride_at,writes_bar,duplex,aligned_apply,joinLin_apply]

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem scanner_inj (d : ℕ) (b : Module.Basis ι ℂ (W d)) (x y : E4) (hx : x≠y) :
    Injective (fun v : W d => fun i => readsTwo F d x y v (b i)) := by
  intro v w he
  by_contra h
  let B := readsTwo F d x y
  have hz : B v = B w := b.ext (fun i => congr_fun he i)
  have hp := faceTest_eq F d x y (v-w) (v-w)
  have he : 0 < duplex x y (writes F d (v-w)) (writes F d (v-w)) :=
    (reflected_positive hx _).2 (by rw [map_sub]; exact sub_ne_zero.mpr ((writes_inj F d).ne h))
  change B (v-w) _ = _ at hp
  rw [map_sub,hz,sub_self] at hp
  rw [← hp] at he; simp at he





/-- Actual pair template at the same generic displacement. Can select x,y
before arranging apertures. -/
def colPair (b : Type*) (i : b) (x y : E4) (hx : couple x y ∈ generic 2) : Cells.SampleRow b :=
    ⟨1,le_rfl,(fun _ => i),couple x y,hx⟩


end YM.Extra.FD
