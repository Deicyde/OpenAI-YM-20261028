import Mathlib.RingTheory.Nilpotent.Exp
import YM.Push.CORRECTED_COLUMNS.Program

/-!
# Geometry and cost input examples for Meeting

 common endpoint cubes. Intermediate *l* level explicitly.
Along N beyond the positions, moment seam copies remember their
anchor and are in this k-grid, including through link seams. At a
sufficiently fine such of the sequence (eventually in its index k)
the ENTIRE set of marks in a coarse rank cell places to one l-site.
No appeals to point convergence through projection ties.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Point
open Filter Function Set Lattice RG Wilson MeasureTheory Marker Cells Extraction
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G}
variable (B : Series C)

abbrev middle (k : ℕ) := B.depth k-Zone.boxes (lvl C) B.b (B.depth k)
lemma credit (k) : B.side k≤middle B k := Nat.sub_le_sub_left (Nat.le_add_right ..) _
lemma debits (k) : middle B k≤B.depth k := Nat.sub_le ..

lemma size (k : ℕ) : C.S.a (B.depth k)*(Zone.factor (lvl C) (B.depth k):ℝ)^Zone.boxes (lvl C) B.b (B.depth k)=C.S.a (middle B k) := by
  let z := Zone.factor (lvl C) (B.depth k)
  let d := Zone.boxes (lvl C) B.b (B.depth k)
  let l := middle B k
  have hz : 0 < (z:ℝ) := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (by exact_mod_cast Zone.exp_size _ _ (B.h k).positive)
  have he : l+d=B.depth k := Nat.sub_add_cancel ((Nat.le_add_right ..).trans (B.h k).onward)
  have ht (i : ℕ) (hi : i≤d) : C.S.a (l+i)*(z:ℝ)^i=C.S.a l := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [← Nat.add_assoc,C.S.a_step,pow_succ]
      have hL : (C.S.block (l+i)).val=z := by
        unfold z Zone.factor; rw [← (B.h k).plateau (l+i+1) ((credit B k).trans (show l ≤ _ by omega)) (by omega),
          ← (lvl C).fits.sameFactor (l+i)]
      rw [hL,show C.S.a (l+i)/(z:ℝ)*((z:ℝ)^i * z) = C.S.a (l+i) * (z:ℝ)^i by field_simp]
      exact ih (by omega)
  simpa only [he] using ht d le_rfl










end YM.Push.Corrected.Point
