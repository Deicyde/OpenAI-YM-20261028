import YM.Pert.Lattice.Cubical
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
/-! Character convention on the finite top torus. -/
noncomputable section
namespace YM.Pert.Full
open Lattice Function Complex BigOperators
variable {n : Side}

def dot (p x : Site n) : Per n := ∑ i, p i * x i
def char (p x : Site n) : ℂ := ZMod.stdAddChar (dot p x)
def incVec (r : ℝ) (x : Cover) : E4 := WithLp.toLp 2 (fun i => r*(x i : ℝ))
def mesh (n : Side) : ℝ := 2 * Real.pi / n.val
def moment (p : Site n) : E4 := incVec (mesh n) (lift p)
lemma val_pos (n : Side) : 0 < (n.val : ℝ) := by exact_mod_cast n.pos
@[simp] lemma incVec_apply (r : ℝ) (x : Cover) (i : Axis) : incVec r x i = r * x i := rfl
@[simp] lemma moment_apply (p : Site n) (i : Axis) : moment p i = mesh n * (lift p i : ℝ) := rfl
lemma mesh_pos : 0 < mesh n := by unfold mesh; positivity
lemma mesh_val : mesh n * n.val = 2 * Real.pi := by unfold mesh; field_simp
lemma moment_cube (p : Site n) : moment p ∈ cube := by
  intro i; rw [moment_apply]; have low : - (n.val : ℝ) < 2*(lift p i:ℝ) := by exact_mod_cast (lift_centers p i).1
  have high : 2*(lift p i:ℝ) ≤ (n.val:ℝ) := by exact_mod_cast (lift_centers p i).2
  apply abs_le.mpr; have hm := mesh_pos (n:=n); have e := mesh_val (n:=n); constructor
  · nlinarith
  nlinarith
lemma moment_ne {p : Site n} (hp : p ≠ 0) : moment p ≠ 0 := by
  intro he; have eh (i : Axis) := congrArg (fun x : E4 => x i) he
  apply hp
  rw [← wrap_lift p]; have h : lift p = 0 := by
    ext i; have hv := eh i; change mesh n * (lift p i : ℝ) = 0 at hv
    have hz := (mul_eq_zero.mp hv).resolve_left mesh_pos.ne'; exact_mod_cast hz
  rw [h,map_zero]
lemma char_zero (p : Site n) : char p 0 = 1 := by unfold char dot; simp
lemma zero_char (x : Site n) : char 0 x = 1 := by unfold char dot; simp
lemma swap (p x : Site n) : char p x = char x p := by unfold char dot; simp_rw [mul_comm]
lemma dot_add (p x y : Site n) : dot p (x+y) = dot p x + dot p y := by simp only [dot, Pi.add_apply,mul_add,Finset.sum_add_distrib]
lemma char_add (p x y : Site n) : char p (x+y) = char p x * char p y := by unfold char; rw [dot_add, AddChar.map_add_eq_mul]
lemma dot_wrapped (p : Site n) (x : Cover) : dot p (wrap n x) = ↑(∑ i, (lift p i)*(x i):ℤ) := by
  calc _ = dot (wrap n (lift p)) (wrap n x) := by rw [wrap_lift]
    _ = _ := by simp [dot,wrap]
lemma char_wrapped (p : Site n) (x : Cover) : char p (wrap n x) = Complex.exp ((corner x (moment p) : ℂ)*I) := by
  rw [char,dot_wrapped,ZMod.stdAddChar_coe]
  unfold corner
  congr 1
  push_cast
  rw [Finset.sum_mul]; simp_rw [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i hi; push_cast; simp only [moment_apply,mesh, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat, Complex.ofReal_natCast]; ring
lemma corner_step (i : Axis) (p : E4) : corner (step i) p = p i := by simp [corner, Finset.sum_ite_irrel,step,Pi.single_apply]
lemma char_step (p : Site n) (i : Axis) : char p (step i) = Complex.exp ((moment p i)*I) := by simpa only [corner_step, wrap_step] using char_wrapped p (step i)
lemma char_neg_step (p : Site n) (i : Axis) : char p (- step i) = Complex.exp (-((moment p i)*I)) := by
  have hn : corner (-step i) (moment p) = -(moment p i) := by rw [← corner_step i]; simp [corner, neg_mul]
  simpa only [hn, map_neg, wrap_step, Complex.ofReal_neg, neg_mul] using char_wrapped p (-step i)
lemma scan (p : Site n) : ∑ x : Site n, char p x = if p=0 then (n.val:ℂ)^4 else 0 := by
  split
  next h => rw [h]; simp [zero_char,site_card]
  next h =>
    suffices hz : ∃ y : Site n, char p y ≠ 1 by
      obtain ⟨y,hy⟩ := hz
      have he := Equiv.sum_comp (Equiv.addRight y) (char p)
      change ∑ i, char p (i+y) = _ at he
      simp_rw [char_add, ← Finset.sum_mul] at he
      by_contra hz; exact hy ((mul_eq_left₀ hz).mp he)
    by_contra! h'
    apply h; ext i
    have he := h' (step i); unfold char at he; rw [← (ZMod.stdAddChar (N:=n.val)).map_zero_eq_one] at he; apply ZMod.injective_stdAddChar at he
    rw [dot, Finset.sum_eq_single i] at he <;> simp_all [step_apply,eq_comm]
lemma norm_char (p x : Site n) : ‖char p x‖ = 1 := Circle.norm_coe _
end YM.Pert.Full
