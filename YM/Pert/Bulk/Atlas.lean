import YM.Pert.Bulk.Sites

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Stationary Laurent RG
open scoped Topology BigOperators Classical ENNReal

/-- Absolute coefficient majorant. -/
def bill (x w : ℝ) := ENNReal.ofReal (|x| * Real.exp w)
lemma bill_eq (x w : ℝ) : bill x w = ENNReal.ofReal |x| * ENNReal.ofReal (Real.exp w) := ENNReal.ofReal_mul (abs_nonneg _)
lemma bill_mono {x y t u : ℝ} (h : |x| ≤ |y|) (ht : t≤u) : bill x t ≤ bill y u := by unfold bill; apply ENNReal.ofReal_le_ofReal; gcongr
lemma bill_sub (x y t : ℝ) : bill (x-y) t ≤ bill x t + bill y t := by
 rw [bill,bill,bill, ← ENNReal.ofReal_add (by positivity : 0≤ |x| * Real.exp t) (by positivity), ← add_mul]
 exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (abs_sub x y) (by positivity))
lemma bill_add (x t s : ℝ) : bill x (t+s) = bill x t * ENNReal.ofReal (Real.exp s) := by simp only [bill,Real.exp_add,ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
lemma bill_width_sum {X : Type} {f:X→ℝ} {w:X→ℝ} {C:ℝ} (h:SumBudget (fun x => |f x| *Real.exp (w x)) C) : ∑' x, bill (f x) (w x) ≤ ENNReal.ofReal C :=
  (show ∑' x,bill _ _ = _ from (ENNReal.ofReal_tsum_of_nonneg h.1 h.2.1).symm).trans_le (ENNReal.ofReal_le_ofReal h.2.2)
lemma bill_sum_le (X:Type) (f:X→ℝ) (s t) (ht:t≤s) :
   ∑' x, bill (f x) t ≤ ∑' x,bill (f x) s := ENNReal.tsum_le_tsum (fun _ => bill_mono (by rfl) ht)
lemma bill_ne_top {X:Type} {f w:X→ℝ} (h : ∑' x,bill (f x) (w x) ≠⊤) : Summable (fun x => |f x| *Real.exp (w x)) := (ENNReal.summable_toReal h).congr fun x => ENNReal.toReal_ofReal (by positivity)
lemma summable_from_receipt {X:Type} {f w:X→ℝ} (hw : ∀ x,0≤ w x) (h : ∑' x,bill (f x) (w x) ≠⊤) : Summable f := (Summable.of_nonneg_of_le (g:=fun x=> ‖f x‖) (by intros; positivity) (fun x => by simpa using le_mul_of_one_le_right (abs_nonneg (f x)) (Real.one_le_exp (hw x))) (bill_ne_top h)).of_norm

abbrev Market (α : Type) := Cover × α
abbrev Kernel (α β : Type) := Market α → Market β → ℝ
variable {α β : Type} {L : Side}

def RowCost (σ : ℝ) (L : Side) (T : Kernel α β) (p:ℝ) :=
 ∀ (u:Market α) (j:β), ∑' y, bill (T u (y,j)) (σ*delta L u.1 y) ≤ ENNReal.ofReal p

def ColCost (σ : ℝ) (L : Side) (T : Kernel α β) (p:ℝ) :=
 ∀ (i:α) (u:Market β), ∑' x, bill (T (x,i) u) (σ*delta L x u.1) ≤ ENNReal.ofReal p

def foot (k:Axis) (f:Kernel α β) : Kernel α β := fun v w => f (v.1+Lattice.step k,v.2) w - f v w

/-- Row and column bounds at true lifted sites. `step` is on fine translations. -/
structure Atlas (σ : ℝ) (L : Side) (m : ℕ) (T : Kernel α β) (p:ℝ) : Prop where
 width : 0 ≤ σ
 nonneg : 0≤ p
 row : RowCost σ L T (p/(L.val:ℝ)^m)
 col : ColCost σ L T (p*(L.val:ℝ)^4/(L.val:ℝ)^m)
 step : ∀ i, RowCost σ L (foot i T) (p/(L.val:ℝ)^(m+1))

lemma RowCost.mono {σ θ p:ℝ} {T : Kernel α β} (h : RowCost θ L T p) (hθ : σ≤θ) : RowCost σ L T p :=
  fun u i => (ENNReal.tsum_le_tsum fun _ => bill_mono le_rfl (mul_le_mul_of_nonneg_right hθ (delta_nonneg ..))).trans (h u i)
lemma ColCost.mono {σ θ p:ℝ} {T : Kernel α β} (h : ColCost θ L T p) (hθ : σ≤θ) : ColCost σ L T p :=
  fun i u => (ENNReal.tsum_le_tsum fun _ => bill_mono le_rfl (mul_le_mul_of_nonneg_right hθ (delta_nonneg ..))).trans (h i u)
lemma Atlas.mono {σ θ p:ℝ} {m:ℕ}{T : Kernel α β} (h : Atlas θ L m T p) (hθ : σ≤θ) (hp:0≤σ) : Atlas σ L m T p := ⟨hp,h.nonneg,h.row.mono hθ,h.col.mono hθ,fun i => (h.step i).mono hθ⟩
end YM.Pert.Bulk
