import YM.Extra.ITERATION_NO_LOSS.Sums
import YM.Work.B04

/-!
# True-length canonical path budgets
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Lattice Wilson RG Function
open scoped Topology BigOperators

variable {G : Gauge} {k : ℕ} {ι : Type*}

lemma step_size (d : Step) : Laurent.size (d.vec : Cover) = 1 := by
  have h : Laurent.size (step d.dir : Cover) = 1 := by simp [Laurent.size, step_apply, apply_ite Int.natAbs]
  unfold Step.vec; split
  · rw [Laurent.size_neg, h]
  exact h

lemma end_size (x : Cover) (w : Walk) : Laurent.size (stop x w) ≤ Laurent.size x + w.length := by
  induction w generalizing x with
  | nil => exact Nat.le_refl _
  | cons d w ih =>
    refine (ih _).trans ?_; have h := Laurent.size_add x (Step.vec d); rw [step_size] at h
    simp only [List.length_cons]; omega

lemma along_size (x y : Cover) (w : Walk) (h : y∈ visits x w) : Laurent.size (y-x) ≤ w.length := by
  induction w generalizing x with
  | nil => rw [show y = x by simpa [visits] using h]; simp [Laurent.size]
  | cons d w ih =>
    rcases List.mem_cons.mp h with rfl|h
    · simp [Laurent.size]
    have ht := ih _ h
    rw [← sub_add_sub_cancel y (x+d.vec) x,add_sub_cancel_left]; exact (Laurent.size_add _ _).trans
      (by rw [step_size,List.length_cons]; omega)

lemma route_length (x y : Cover) (o : Lattice.Order) : (route x y o).length = Laurent.size (y-x) := by
  have hl : (allAxes o).Nodup := (List.nodup_finRange 4).map o.injective
  have he : (allAxes o).toFinset = Finset.univ := Finset.eq_univ_of_forall fun i =>
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨o.symm i,by simp,by simp⟩)
  simp only [route, axisRoute, List.length_flatMap, straight, List.length_replicate]
  rw [← List.sum_toFinset (fun a => (y a-x a).natAbs) hl, he]; rfl

lemma offset_size (s : Slot) : Laurent.size s.offset ≤ s.walk.length := by simpa only [Slot.offset,Laurent.size, Pi.zero_apply,Int.natAbs_zero,Finset.sum_const_zero,zero_add] using end_size 0 s.walk

lemma coeff_le (a : Atom G k) (b) : |a.coeff b| ≤ a.magnitude :=
  Finset.single_le_sum (fun b _ => abs_nonneg (a.coeff b)) (Finset.mem_univ b)

/-- Fixed inverse-paired tie order in unshifted coordinates (no orientation
invariance needed of the tie breaker itself). -/
def tie (x : Cover) : Lattice.Order := if Encodable.encode x ≤ Encodable.encode (-x) then 1 else backOrder 1

def slot (x : Cover) (b : PlaqAxes) : Slot := ⟨route 0 x (tie x), b⟩

@[simp] lemma slot_offset (x b) : (slot x b).offset = x := route_end ..
@[simp] lemma slot_length (x b) : (slot x b).length = Laurent.size x + 4 := by rw [Slot.length,slot,route_length,sub_zero]
@[simp] lemma slot_plaq (x b) : (slot x b).plaq = b := rfl

/-- New path choices in a common positive-orientation channel; later take the
full action average. Never period-local shortest paths. -/
def relocate (a : Atom G k) (u : ℝ) (x : Fin k → Cover) (b : Fin k → PlaqAxes) : Atom G k where
  leg i := slot (x i) (b i)
  coeff j := u * a.coeff j

lemma relocated_poly (a : Atom G k) (u x b v) : (relocate a u x b).poly v = u * a.poly v := by
  simp only [Atom.poly, relocate, Finset.mul_sum, mul_assoc]

lemma relocated_length (a : Atom G k) (u x b) :
    (relocate a u x b).length = (∑ i, Laurent.size (x i)) + 4*k := by
  simp [Atom.length, relocate, Finset.sum_add_distrib, Nat.mul_comm]

lemma relocated_coeff (a : Atom G k) (u x b) :
    (relocate a u x b).magnitude = |u| * a.magnitude := by
  simp only [Atom.magnitude, relocate, abs_mul, Finset.mul_sum]

lemma relocated_symm (a : Atom G k) (ha : a.Invariant) (u x b) : (relocate a u x b).Invariant := by
  intro g c; rw [relocated_poly, ha, relocated_poly]

/-- Positive path accounting separately from lower jet and gauge requirements. -/
def Charged (A : ι → Atom G k) (σ C : ℝ) := SumBudget (fun i => (A i).budget σ) C

namespace Charged
variable {A : ι → Atom G k} {σ C : ℝ} (h : Charged A σ C)
include h
lemma mono {σ' C' : ℝ} (hs : σ' ≤ σ) (hc : C ≤ C') : Charged A σ' C' := by
  refine Cost.enlarge (Cost.mono h (f:=fun i => (A i).budget σ') ?_ ?_) hc
  · intro i; unfold Atom.budget Atom.magnitude; positivity
  intro i; unfold Atom.budget
  exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hs (by positivity)))
    (by unfold Atom.magnitude; positivity)

lemma moments (s : ℕ) {η : ℝ} (hη : 0 < η) : SumBudget (fun i => (1+((A i).length:ℝ))^s * (A i).budget (σ-η))
    (momentPrice s η * C) := by
  refine Cost.mono (Cost.scale h _ (momentPrice_pos _ hη).le) (fun i => by unfold Atom.budget Atom.magnitude; positivity) fun i => ?_
  calc
    _ ≤ (momentPrice s η * Real.exp (η*(A i).length)) * (A i).budget (σ-η) := mul_le_mul_of_nonneg_right
      (spendMoment _ hη (by positivity)) (by unfold Atom.budget Atom.magnitude; positivity)
    _ = _ := by simp only [Atom.budget, sub_mul, Real.exp_sub]; field_simp

lemma absolute (hs : 0 ≤ σ) : Summable (fun i => (A i).magnitude) := by
  simpa [Atom.budget] using (h.mono hs le_rfl).2.1
end Charged

abbrev SymmetricAtoms (A : ι → Atom G k) : Prop := ∀ i, (A i).Invariant

def join (A B : ℕ → Atom G k) : ℕ → Atom G k := Sum.elim A B ∘ numbering (ℕ ⊕ ℕ)
lemma join_sym {A B : ℕ → Atom G k} (h : SymmetricAtoms A) (hh : SymmetricAtoms B) : SymmetricAtoms (join A B) := by
  intro i; unfold join comp; cases numbering (ℕ ⊕ ℕ) i <;> [apply h; apply hh]
lemma join_cost {A B : ℕ → Atom G k} {σ C D : ℝ} (h : Charged A σ C) (hh : Charged B σ D) :
    Charged (join A B) σ (C+D) := Cost.equiv _ (Cost.sum (f:=fun i => (Sum.elim A B i).budget σ) h hh)

def blank (G : Gauge) (k : ℕ) : Atom G k := ⟨fun _ => ⟨[],Classical.arbitrary _⟩,0⟩
lemma blank_sym : (blank G k).Invariant := by simp [Atom.Invariant,Atom.poly,blank]
lemma blank_cost (σ : ℝ) : Charged (fun _ : ι => blank G k) σ 0 := by simp [Charged, SumBudget, Atom.budget,Atom.magnitude,blank]

def charge (a : Atom G 2) (i : Fin 2 → PlaqAxes) (b : Fin 2 → G.ColorIndex) :=
  if (fun k => (a.leg k).plaq) = i then a.coeff b else 0

def delta (a : Atom G 2) := (a.leg 1).offset - (a.leg 0).offset
lemma delta_size (a : Atom G 2) : Laurent.size (delta a) ≤ a.length := by
  unfold delta; rw [sub_eq_add_neg, Atom.length, Fin.sum_univ_two]
  have ht := offset_size (a.leg 0); have hh := offset_size (a.leg 1)
  apply (Laurent.size_add _ _).trans; rw [Laurent.size_neg]; unfold Slot.length; omega

/-- Vanishing loop curvature value and first jets (not potential jets), on
unwrapped linear translation coefficients. Separate from the numerical price. -/
def Silent (A : ι → Atom G 2) := ∀ i b, HasSum (fun p => charge (A p) i b) 0 ∧
    ∀ l : Axis, HasSum (fun p => charge (A p) i b * delta (A p) l) 0
lemma blank_silent : Silent (fun _ : ι => blank G 2) := by
  simp [Silent,charge,blank]
lemma join_silent {A B : ℕ → Atom G 2} (ha : Silent A) (hb : Silent B) : Silent (join A B) := by
  intro i b
  let f := numbering (ℕ ⊕ ℕ)
  have h0 := HasSum.sum (f:=fun p => charge (Sum.elim A B p) i b) (ha i b).1 (hb i b).1
  have h1 (l : Axis) := HasSum.sum (f:=fun p => charge (Sum.elim A B p) i b * delta (Sum.elim A B p) l)
    ((ha i b).2 l) ((hb i b).2 l)
  simp only [zero_add] at h0 h1
  exact ⟨(f.hasSum_iff (f:=fun p => charge (Sum.elim A B p) i b)).2 h0, fun l =>
    (f.hasSum_iff (f:=fun p => charge (Sum.elim A B p) i b * delta (Sum.elim A B p) l)).2 (h1 l)⟩

lemma silent_of_bounds {W : PathData G} {p σ C Λ} (h : W.Bounds p σ C Λ) : Silent W.loop := by
  intro i b; have ht := h.loopTerms i b; have hh := h.loop_normal i b
  exact ⟨hh.1 ▸ ht.1.hasSum,fun l => hh.2 l ▸ (ht.2 l).hasSum⟩
end YM.Extra.Iteration
