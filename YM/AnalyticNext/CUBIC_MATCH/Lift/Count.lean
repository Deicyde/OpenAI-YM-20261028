import YM.Analysis.Polydisc
import YM.Next.FREE_KERNELS.Signal
import YM.Pressure.Seeds


set_option warningAsError false

/-!
# Pointwise decay wrappers

For intermediate exterior lift bounds use price times a pointwise rate in
native edge lengths on the cover. In the end we pay the counting price and
actual exponential support length; the sup version doesn't replace it. All
rates used for decay are *positive*. Power notation not relying on local
`ℕ` distances default.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch

open Filter Function Lattice RG Matrix Bloch Laurent Exterior Next
open scoped Topology ContDiff BigOperators

variable {E : Type*} [SeminormedAddCommGroup E] {ι : Type*} {f g : ι → E} {L : ι → ℕ} {η C D θ : ℝ}

def wanes (η : ℝ) (r : ℕ) := Real.exp (-η*r)

/-- Works for rows and coefficients with finite passive type indices. -/
def Decay (L : ι → ℕ) (η C : ℝ) (f : ι → E) := ∀ i, ‖f i‖ ≤ C*wanes η (L i)

lemma wanes_pos (η : ℝ) (r : ℕ) : 0 < wanes η r := Real.exp_pos _
lemma wanes_splits (η : ℝ) (r s : ℕ) : wanes η (r+s)=wanes η r*wanes η s := by
  unfold wanes; push_cast; rw [mul_add,Real.exp_add]

lemma wanes_cost (hη : 0 ≤ η) (x y : Cover) :
    wanes η (size x) ≤ Real.exp (η*size y)*wanes η (size (x+y)) := by
  unfold wanes; rw [← Real.exp_add]; apply Real.exp_monotone
  have hh : η*size (x+y) ≤ η*(size x+(size y:ℝ)) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast size_add x y) hη
  linarith

theorem wanes_summable (hη : 0 < η) : Summable fun x : Cover => wanes η (size x) :=
  (Width.compactPay _ hη).2.1

lemma Decay.mono (h : Decay L η C f) (hθ : θ ≤ η) (hD : C ≤ D) (hp : 0 ≤ D) : Decay L θ D f :=
  fun i => (h i).trans ((mul_le_mul_of_nonneg_right hD (wanes_pos ..).le).trans <|
    mul_le_mul_of_nonneg_left (Real.exp_monotone <| mul_le_mul_of_nonneg_right (neg_le_neg hθ) (by positivity)) hp)
lemma Decay.enlarge (h : Decay L η C f) (hp : C ≤ D) : Decay L η D f :=
  fun i => (h i).trans (mul_le_mul_of_nonneg_right hp (wanes_pos ..).le)
lemma Decay.cash [Nonempty ι] (h : Decay L η C f) : 0 ≤ C :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (h (Classical.arbitrary ι))) (wanes_pos ..)
lemma Decay.plus (h : Decay L η C f) (p : Decay L η D g) : Decay L η (C+D) (f+g) := fun i =>
  (norm_add_le (f i) (g i)).trans ((add_le_add (h i) (p i)).trans_eq (add_mul ..).symm)
lemma Decay.minus (h : Decay L η C f) (p : Decay L η D g) : Decay L η (C+D) (f-g) := fun i =>
  (norm_sub_le (f i) (g i)).trans ((add_le_add (h i) (p i)).trans_eq (add_mul ..).symm)
lemma Decay.scaled [NormedSpace ℝ E] (h : Decay L η C f) (a : ℝ) : Decay L η (|a| * C) (a • f) := by
  intro i; simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_assoc]; exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
lemma Decay.fin {μ : Type*} {A : μ → ι → E} {p : μ → ℝ} {s : Finset μ} (h : ∀ i∈s, Decay L η (p i) (A i)) :
    Decay L η (∑ i∈s,p i) (fun a => ∑ i∈s, A i a) := by
  intro x; exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i g => h i g x)).trans_eq
    (Finset.sum_mul ..).symm)
lemma Decay.summable_norm (h : Decay L η C f) (hp : Summable fun i => wanes η (L i)) :
    Summable (fun i => ‖f i‖) :=
  Summable.of_nonneg_of_le (fun i => norm_nonneg (f i)) h (hp.mul_left C)

abbrev Couple := Cover × Cover

def length2 (p : Couple) := size p.1+size p.2

lemma summable_two (hη : 0 < η) : Summable fun i : Couple => wanes η (length2 i) := by
  let a (i : Cover) := wanes η (size i)
  have ha : Summable a := wanes_summable hη
  have he : 0 ≤ a := fun i => show 0 ≤ wanes η (size i) from (wanes_pos ..).le
  exact (Summable.mul_of_nonneg ha ha he he).congr (fun i => (wanes_splits _ _ _).symm)

lemma sub_decay (hη : 0 ≤ η) (x y : Couple) : wanes η (length2 (x-y)) ≤
    Real.exp (η*(length2 y))*wanes η (length2 x) := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  simp only [length2, Prod.fst_sub, Prod.snd_sub,wanes_splits,Nat.cast_add,mul_add,Real.exp_add]
  have he (x y : Cover) := wanes_cost hη (x-y) y
  simp only [sub_add_cancel] at he
  exact (mul_le_mul (he a c) (he b d) (wanes_pos ..).le (mul_nonneg (Real.exp_pos _).le (wanes_pos ..).le)).trans_eq (by ring)
end YM.CubicMatch
