import Mathlib.MeasureTheory.Group.IntegralConvolution
import YM.Cells.Packing
import YM.Complex.Gaps


/-!
# Which centered bounds are needed

Pointwise-transfer proof uses all fixed periods. Use CenteredBook for EACH
AND eventual period. Derive using explicit main canonical estimate and
(eventual volume only) cells hypothesis. Never silently promote.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Filter Set MeasureTheory Lattice Wilson Cells
open scoped Topology BigOperators ComplexOrder Matrix.Norms.Frobenius

variable {G : Gauge} (C : Family G) (f : Order)

def centeredBudget (v : C.book.Token) (A : ℝ) (m N p : ℕ) : Prop := ∃ h : m ≤ N,
    C.ref v.1 ≤ N ∧ ∀ o : Site (C.side N p), Interior ((center C.S p h o).chamber 0) (C.seen v o) ∧
    (center C.S p h o).rootTest (C.beta N p) (C.seen v o) ≤ A

structure CenteredBook : Prop where
  each (v : C.book.Token) (p : ℕ) : ∀ᶠ m in atTop, ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ j in atTop,
    centeredBudget C v A m (f.mesh j) p
  expanding (v : C.book.Token) : ∀ᶠ m in atTop, ∃ A : ℝ, 0 ≤ A ∧ f.late (centeredBudget C v A m)

structure CenterPort : Prop where

  per (v : C.book.Token) (p : ℕ) : ∀ᶠ m in atTop, ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ j in atTop,
    centeredBudget C v A m (f.mesh j) p
  cells : CellHyp C f

/-- Candidate red bootstrap strength: a literal estimate in the schedule, not
upon eventual extraction. Positivity transfer separate. -/
def Wcmain (C : Family G) := ∀ d (R ε : ℝ), 0 < R → 0 < ε → ∃ A : ℝ, 0 ≤ A ∧ ∀ m,
    C.ref d ≤ m → ∀ᶠ N in atTop, ∀ p, ∀ v : C.book.Ref d, ‖v‖ ≤ R →
    centeredBudget C ⟨d,v⟩ (A*C.S.a m^(-(d:ℝ)-ε)) m N p

lemma Wcmain.projects (h : C.Makes) (H : Wcmain C) : CenterPort C f := by
  constructor
  · rintro ⟨d,v⟩ p
    obtain ⟨A,hA,ht⟩ := H d (‖v‖+1) 1 (by positivity) (by norm_num)
    filter_upwards [eventually_ge_atTop (C.ref d)] with m he
    exact ⟨_,mul_nonneg hA (Real.rpow_nonneg (C.S.a_pos m).le _),
      (f.mesh.cofinal.eventually (ht m he)).mono fun j hj => hj p v (by simp)⟩
  refine ⟨seamless h,?_⟩
  intro d ε R he hr
  obtain ⟨A,H,hh⟩ := H d R ε hr he
  refine ⟨C.ref d,le_rfl,A,H,fun m hm η hp => Eventually.of_forall fun i => ?_⟩
  filter_upwards [f.mesh.cofinal.eventually (eventually_ge_atTop m), f.mesh.cofinal.eventually (hh m hm)] with j h hu
  refine ⟨h,fun v hv u => ?_⟩
  obtain ⟨hn,hD,hF⟩ := hu (f.per i) v hv
  exact ⟨(hF u).1, (hF u).2.trans (le_add_of_nonneg_right hp.le)⟩

lemma CenterPort.book (h : CenterPort C f) : CenteredBook C f := by
  refine ⟨h.per,?_⟩
  rintro ⟨d,v⟩
  obtain ⟨m₀,H,A,hA,η⟩ := h.cells.centered d 1 (‖v‖+1) (by norm_num) (by positivity)
  filter_upwards [eventually_ge_atTop m₀] with m hm
  refine ⟨_, add_nonneg (mul_nonneg hA (Real.rpow_nonneg (C.S.a_pos m).le (- (d : ℝ)-1))) zero_le_one, ?_⟩
  exact (η m hm 1 (by norm_num)).mono fun i hi => hi.mono fun j hj => by
    obtain ⟨w,hj⟩ := hj
    exact ⟨w,H.trans (hm.trans w),fun o => hj v (by simp) _⟩

lemma fixup {v : C.book.Token} {a b : ℝ} {m N p} (he : centeredBudget C v a m N p) (hw : a≤b) :
    centeredBudget C v b m N p := by
  obtain ⟨h,h₁,h₂⟩ := he
  exact ⟨h,h₁,fun x => ⟨(h₂ x).1,(h₂ x).2.trans hw⟩⟩

/-- Turn into budgets for an entire finite tuple -/
lemma lib {ι : Type*} (I : Finset ι) (H : CenteredBook C f) (p : ℕ) (w : ι → C.book.Token) :
    (∀ᶠ m in atTop, ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ j in atTop, ∀ i∈I, centeredBudget C (w i) A m (f.mesh j) p) ∧
    (∀ᶠ m in atTop, ∃ A : ℝ, 0 ≤ A ∧ f.late fun N p => ∀ i∈I, centeredBudget C (w i) A m N p) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨Eventually.of_forall fun _ => ⟨0,le_rfl,by simp⟩, Eventually.of_forall fun _ => ⟨0,le_rfl,by simp [Order.late]⟩⟩
  | @insert i t hi ih =>
    constructor
    · filter_upwards [H.each (w i) p,ih.1] with m hm hv
      obtain ⟨P,hP,H⟩ := hm; obtain ⟨Q,hq,T⟩ := hv
      refine ⟨max P Q,(hP.trans (le_max_left ..)),?_⟩
      filter_upwards [H,T] with j hj ht x he
      rcases Finset.mem_insert.mp he with h|h
      · subst x; exact fixup C hj (le_max_left ..)
      exact fixup C (ht x h) (le_max_right ..)
    filter_upwards [H.expanding (w i),ih.2] with m hm hv
    obtain ⟨P,hP,H⟩ := hm; obtain ⟨Q,hq,T⟩ := hv
    refine ⟨max P Q,(hP.trans (le_max_left ..)),?_⟩
    exact (H.and T).mono fun i hi => (hi.1.and hi.2).mono fun j hj x h => by
      rcases Finset.mem_insert.mp h with h|h
      · subst x; exact fixup C hj.1 (le_max_left ..)
      exact fixup C (hj.2 x h) (le_max_right ..)

end YM.Extraction
