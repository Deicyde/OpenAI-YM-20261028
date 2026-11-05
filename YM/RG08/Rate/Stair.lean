import YM.Lattice.Scale
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Formal UV iteration: conventions for uniform receipts

`Stair X`: one scheduling problem. X = range of all parameters in which the answer is
required uniform (including top or compatible pair of tops). Can also index a class of schedules,
not only one fixed calendar. Fixed finite demand (field/perturbative horizon, geometric caps...)
is *outside* this X. Use X subtypes for any admissibility/arrival assumptions on the formal
steps. `Poly` and `Fade` on array *upper costs* only -- use abs/norm on the function side first!

S.scale is log inverse spacing with zero at level zero; S.block i is for step i+1→i.
-/
noncomputable section
namespace YM.RG08.Rate
open Filter Real
open scoped Topology

set_option autoImplicit false
universe v

structure Stair (X : Type v) where
  sched : X → Schedule
  low : X → ℕ
  top : X → ℕ
  k : X → ℕ
  Z : X → ℝ
  Z_nonneg x : 0 ≤ Z x

namespace Stair
variable {X : Type v} (W : Stair X)

def Here (x : X) (i : ℕ) : Prop := W.low x ≤ i ∧ i ≤ W.top x

def time (x : X) (i : ℕ) := (W.sched x).scale i
def length (x : X) (i : ℕ) : ℝ := ((W.sched x).block i).val
def age (x : X) (i : ℕ) := 2 + W.Z x + |W.time x i - W.time x (W.k x)|

theorem length_large (x : X) (i : ℕ) : 3 ≤ W.length x i := by
  unfold length
  exact_mod_cast (W.sched x).block_large i
@[simp] theorem time_step (x : X) (i : ℕ) : W.time x (i+1) = W.time x i + Real.log (W.length x i) := (W.sched x).scale_succ _

theorem sep_step (x : X) (i : ℕ) : Real.log 3 ≤ W.time x (i+1)-W.time x i := by
  rw [time_step, add_sub_cancel_left]
  exact Real.log_le_log (by norm_num) (length_large ..)

theorem time_strict (x : X) : StrictMono (W.time x) := by
  apply strictMono_nat_of_lt_succ
  intro j
  linarith only [W.sep_step x j, Real.log_pos (show (1:ℝ)<3 by norm_num)]

theorem age_big (x : X) (i : ℕ) : 2 ≤ W.age x i := by
  unfold age
  linarith [W.Z_nonneg x, abs_nonneg (W.time x i-W.time x (W.k x))]

theorem age_later (x : X) (i j : ℕ) (h : i ≤ j) : W.age x j ≤ W.age x i + (W.time x j - W.time x i) := by
  unfold age
  have e:= abs_sub_le (W.time x j) (W.time x i) (W.time x (W.k x))
  rw [abs_of_nonneg (sub_nonneg.mpr ((W.time_strict x).monotone h))] at e
  linarith

def weight (θ : ℝ) (x : X) (i : ℕ) := Real.exp (θ * (W.time x (W.top x) - W.time x i))
def drop (θ : ℝ) (x : X) (i : ℕ) := Real.exp (-θ * (W.time x (i+1) - W.time x i))

theorem drop_pos (θ : ℝ) (x : X) (i : ℕ) : 0 < W.drop θ x i := Real.exp_pos _
theorem weight_pos (θ : ℝ) (x : X) (i : ℕ) : 0 < W.weight θ x i := Real.exp_pos _
theorem weight_big {θ : ℝ} {x : X} {i : ℕ} (ht : i ≤ W.top x) (hθ : 0 ≤ θ) : 1 ≤ W.weight θ x i := Real.one_le_exp (mul_nonneg hθ (sub_nonneg.mpr ((W.time_strict x).monotone ht)))
theorem weight_step (θ c : ℝ) (x : X) (i : ℕ) :
    W.drop θ x i * W.weight c x i = W.drop (θ-c) x i * W.weight c x (i+1) := by
  unfold drop weight
  rw [← Real.exp_add, ← Real.exp_add]; ring_nf

theorem drop_mono (x : X) (i : ℕ) {θ c : ℝ} (h : c ≤ θ) : W.drop θ x i ≤ W.drop c x i :=
  Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg h) ((W.sep_step x i).trans' (Real.log_nonneg (by norm_num))))

theorem drop_length (x : X) (i : ℕ) (θ : ℝ) : W.drop θ x i = W.length x i ^ (-θ) := by
  unfold drop
  have hp : 0 < W.length x i := lt_of_lt_of_le (by norm_num) (W.length_large x i)
  rw [time_step, add_sub_cancel_left, Real.rpow_def_of_pos hp, mul_comm]

theorem weight_length (θ : ℝ) (x : X) (i : ℕ) :
    W.weight θ x i = W.length x i ^ θ * W.weight θ x (i+1) := by
  have hp : 0 < W.length x i := lt_of_lt_of_le (by norm_num) (W.length_large x i)
  unfold weight
  rw [Real.rpow_def_of_pos hp, ← Real.exp_add, time_step]
  ring_nf

theorem weight_inv (θ : ℝ) (x : X) (i : ℕ) :
    (W.weight θ x i)⁻¹ = ((W.sched x).a (W.top x) / (W.sched x).a i)^θ := by
  have hi := (W.sched x).a_pos i
  have ht := (W.sched x).a_pos (W.top x)
  unfold weight time Schedule.scale
  rw [Real.rpow_def_of_pos (div_pos ht hi), Real.log_div ht.ne' hi.ne', Real.log_inv, Real.log_inv, ← Real.exp_neg]
  ring_nf

abbrev Array (X : Type v) := X → ℕ → ℝ

/-- Uniform polynomial costs in the current measuring age, through the entire demanded interval.
Upper AND lower so that costs multiply. Use positive absolute majorants (pad by zero elsewhere). -/
def Poly (f : Array X) := ∃ (A : ℝ) (d : ℕ), 0 ≤ A ∧
   ∀ x i, W.Here x i → 0 ≤ f x i ∧ f x i ≤ A * W.age x i^d

/-- UV cutoff cost: positive power of (top spacing/current spacing) times polynomial age. For two-top
comparisons, `top` is the first boundary (the *coarser* of the top meshes). -/
def Fade (f : Array X) := ∃ θ : ℝ, 0 < θ ∧ W.Poly fun x i => f x i * W.weight θ x i

variable {W} {f g : Array X} {x : X} {i : ℕ}

theorem Poly.nonneg (h : W.Poly f) (hi : W.Here x i) : 0 ≤ f x i := by obtain ⟨A,d,e,t⟩:=h; exact (t x i hi).1
theorem Fade.nonneg (h : W.Fade f) (hi : W.Here x i) : 0 ≤ f x i := by
  obtain ⟨θ,_,ht⟩:= h; exact nonneg_of_mul_nonneg_left (ht.nonneg hi) (W.weight_pos θ x i)

theorem Poly.mono (h : W.Poly f) (hfg : ∀ x i, W.Here x i → 0 ≤ g x i ∧ g x i ≤ f x i) : W.Poly g := by
  obtain ⟨A,d,e,t⟩:=h; exact ⟨A,d,e,fun x i hi=> ⟨(hfg x i hi).1, ((hfg x i hi).2.trans (t x i hi).2)⟩⟩

theorem Fade.mono (h : W.Fade f) (hfg : ∀ x i, W.Here x i → 0 ≤ g x i ∧ g x i ≤ f x i) : W.Fade g := by
  obtain ⟨θ,hθ,e⟩:=h; refine ⟨θ,hθ,e.mono ?_⟩
  exact fun x i hi=> ⟨mul_nonneg (hfg x i hi).1 (W.weight_pos θ x i).le, mul_le_mul_of_nonneg_right (hfg x i hi).2 (W.weight_pos θ x i).le⟩

theorem Fade.poly (h : W.Fade f) : W.Poly f := by
  have hh : ∀ x i, W.Here x i → 0 ≤ f x i := fun _ _ hi=> h.nonneg hi
  obtain ⟨θ,ht,hp⟩:=h
  exact hp.mono fun x i hi=> ⟨hh x i hi, le_mul_of_one_le_right (hh x i hi) (W.weight_big hi.2 ht.le)⟩ -- hh implicit x?

theorem Poly.add (h : W.Poly f) (hg : W.Poly g) : W.Poly fun x i => f x i + g x i := by
  obtain ⟨A,a,hA,ha⟩:=h; obtain ⟨B,b,hB,hb⟩:=hg
  refine ⟨A+B,max a b, add_nonneg hA hB,fun x i hi=>?_⟩
  have hp : 1 ≤ W.age x i := le_trans (by norm_num) (W.age_big x i)
  obtain ⟨hu,hv⟩:= ha x i hi; obtain ⟨hw,hz⟩:= hb x i hi
  exact ⟨add_nonneg hu hw, (add_le_add hv hz).trans (by rw [add_mul]; gcongr <;> simp)⟩

theorem Poly.mul (h : W.Poly f) (hg : W.Poly g) : W.Poly fun x i => f x i * g x i := by
  obtain ⟨A,a,hA,ha⟩:=h; obtain ⟨B,b,hB,hb⟩:=hg
  refine ⟨A*B,a+b,mul_nonneg hA hB,fun x i hi=>?_⟩
  obtain ⟨hz,hz'⟩:=ha x i hi; obtain ⟨hw,hw'⟩:=hb x i hi
  exact ⟨mul_nonneg hz hw,(mul_le_mul hz' hw' hw (hz.trans hz')).trans_eq (by rw [pow_add]; ring)⟩

theorem Poly.constant (W : Stair X) {A : ℝ} (ha : 0 ≤ A) : W.Poly fun _ _ => A :=
  ⟨A,0,ha,fun x i _=> by simp [ha]⟩

theorem Poly.pow (h : W.Poly f) (n : ℕ) : W.Poly fun x i=> f x i^n := by
  induction n with
  | zero => simpa only [pow_zero] using Poly.constant W (zero_le_one' ℝ)
  | succ n hn => simpa only [pow_succ] using hn.mul h

theorem Fade.weaker {θ : ℝ} (hθ : 0 < θ) (ht : W.Poly fun x i => f x i * W.weight θ x i)
    (c : ℝ) (hc : c ≤ θ) : W.Poly fun x i => f x i * W.weight c x i := by
  refine ht.mono fun x i hi=>?_
  have hh : 0 ≤ f x i := Fade.nonneg (show W.Fade f from ⟨θ,hθ,ht⟩) hi
  refine ⟨mul_nonneg hh (W.weight_pos ..).le, mul_le_mul_of_nonneg_left ?_ hh⟩
  unfold weight
  exact Real.exp_monotone (mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr ((W.time_strict x).monotone hi.2)))

theorem Fade.add (h : W.Fade f) (hg : W.Fade g) : W.Fade fun x i => f x i + g x i := by
  obtain ⟨a,ha,h⟩:=h; obtain ⟨b,hb,hg⟩:=hg
  refine ⟨min a b,lt_min ha hb,?_⟩
  simp_rw [add_mul]
  exact (Fade.weaker ha h _ (min_le_left ..)).add (Fade.weaker hb hg _ (min_le_right ..))

theorem Poly.fade (h : W.Poly f) (hg : W.Fade g) : W.Fade fun x i => f x i * g x i := by
  obtain ⟨a,ha,hg⟩:=hg
  refine ⟨a,ha,?_⟩
  simp_rw [mul_assoc]
  exact h.mul hg

theorem Poly.sum {κ : Type*} (t : Finset κ) (f : κ → Array X) (h : ∀ a ∈ t, W.Poly (f a)) : W.Poly fun x i => ∑ a ∈ t, f a x i := by
  classical
  induction t using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using Poly.constant W (le_refl (0:ℝ))
  | insert a t ha ht => simpa only [Finset.sum_insert ha] using (h a (Finset.mem_insert_self ..)).add (ht fun b hb=> h b (Finset.mem_insert_of_mem hb))

theorem Fade.zero (W : Stair X) : W.Fade fun _ _=> 0 :=
  ⟨1,zero_lt_one,by simpa only [zero_mul] using Poly.constant W (le_refl (0:ℝ))⟩

theorem Fade.sum {κ : Type*} (t : Finset κ) (f : κ → Array X) (h : ∀ a ∈ t, W.Fade (f a)) : W.Fade fun x i => ∑ a ∈ t, f a x i := by
  classical
  induction t using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using Fade.zero W
  | insert a t ha ht => simpa only [Finset.sum_insert ha] using (h a (Finset.mem_insert_self ..)).add (ht fun b hb=> h b (Finset.mem_insert_of_mem hb))

end Stair
end YM.RG08.Rate
