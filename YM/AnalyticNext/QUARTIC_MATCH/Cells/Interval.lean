import YM.CellFourier.Mesh

/-!
# Discrete ray primitive and one coordinate homotopy

Primitive on the cover. Don't solve by dividing at torus zero frequency or
asserting finite-period lifting; these cancellations use genuine infinite summation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Function Lattice  Filter Topology
open scoped Topology BigOperators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

namespace Ray

def head (F : ℤ → V) (k : ℤ) := ∑' i, if i≤k then F i else 0
def rest (F : ℤ → V) (k : ℤ) := ∑' i, if k < i then F i else 0

def solution (F : ℤ → V) (b k : ℤ) := if b≤k then rest F k else -head F k
omit [NormedSpace ℝ V] in
lemma head_sums {F : ℤ → V} (h : Summable F) (k : ℤ) : Summable fun i : ℤ => if i≤k then F i else 0 := by
  apply (h.indicator (Set.Iic k)).congr
  intro i; simp [Set.indicator]
omit [NormedSpace ℝ V] in
lemma rest_sums {F : ℤ → V} (h : Summable F) (k : ℤ) : Summable fun i : ℤ => if k < i then F i else 0 := by
  apply (h.indicator (Set.Ioi k)).congr
  intro i; simp [Set.indicator]
omit [NormedSpace ℝ V] in
lemma totals {F : ℤ → V} (h : Summable F) (k : ℤ) : head F k + rest F k = ∑' i,F i := by
  unfold head rest; rw [← (head_sums h k).tsum_add (rest_sums h k)]
  apply tsum_congr; intro i; split_ifs <;> first | omega | simp

omit [NormedSpace ℝ V] in
lemma next {F : ℤ → V} (h : Summable F) (k : ℤ) : F k + head F (k-1) = head F k := by
  unfold head
  let Q (i : ℤ) := if i=k then F k else 0
  have hQ : HasSum Q (F k) := hasSum_ite_eq k (F k)
  nth_rw 1 [← hQ.tsum_eq]
  rw [← hQ.summable.tsum_add (head_sums h (k-1))]; refine tsum_congr fun i => ?_
  unfold Q; split_ifs <;> first | omega | simp_all

omit [NormedSpace ℝ V] in
lemma left {F : ℤ → V} (h : Summable F) (k b : ℤ) :
    solution F b (k-1) - solution F b k = F k - if k=b then (∑' i,F i) else 0 := by
  by_cases hk : k=b
  · subst k; rw [solution, solution,if_neg (by omega),if_pos le_rfl,if_pos rfl, ← totals h b,← next h b]; abel
  rcases lt_or_gt_of_ne hk with hb|hb
  · rw [solution,solution,if_neg (by omega),if_neg (by omega), if_neg hk,← next h k]; abel
  have he m : rest F m = (∑' i,F i) - head F m := by rw [← totals h m]; abel
  rw [solution,solution,if_pos (by omega),if_pos hb.le,if_neg hk,he,he,← next h k]; abel

def jumps (f : ℤ → V) (k : ℤ) := f (k-1)-f k
omit [NormedSpace ℝ V] [CompleteSpace V] in
lemma prev {F : ℤ → V} (h : Summable F) : Summable (fun i => F (i-1)) :=
    (Equiv.subRight (1:ℤ)).summable_iff.mpr h
omit [NormedSpace ℝ V] [CompleteSpace V] in
lemma sumJump {F : ℤ → V} (h : Summable F) : ∑' i,jumps F i=0 := by
  unfold jumps
  rw [(prev h).tsum_sub h,(show (∑' i : ℤ,F (i-1))=∑' i,F i from Equiv.tsum_eq (Equiv.subRight _) F), sub_self]

omit [NormedSpace ℝ V] in
lemma right {F : ℤ → V} (h : Summable F) (k b : ℤ) : solution (jumps F) b k = F k := by
  have he : head (fun i => F (i-1)) k=head F (k-1) := by
    unfold head; rw [← Equiv.tsum_eq (Equiv.subRight (1:ℤ)) (fun i => if i ≤ k-1 then F i else 0)]
    apply tsum_congr; intro i; change _=if i-1 ≤ k-1 then _ else _; split_ifs <;> first | rfl | omega
  have hm : head (jumps F) k=head F (k-1)-head F k := by
    rw [← he]; unfold head; rw [← (head_sums (prev h) k).tsum_sub (head_sums h k)]
    apply tsum_congr; intro i; split_ifs <;> simp [jumps]
  rw [← next h k, show head F (k-1) - (F k+head F (k-1))= -F k by abel] at hm
  unfold solution; split
  · have ha := totals (F:=jumps F) ((prev h).sub h) k
    rw [hm,sumJump h] at ha; exact add_left_cancel (ha.trans (neg_add_cancel _).symm)
  rw [hm,neg_neg]

omit [NormedSpace ℝ V] in
lemma solution_add {F G : ℤ → V} (h : Summable F) (g : Summable G) (b k) :
    solution (F+G) b k=solution F b k+solution G b k := by
  unfold solution; split_ifs
  · unfold rest; rw [← (rest_sums h k).tsum_add (rest_sums g k)]
    apply tsum_congr; intro i; split_ifs <;> simp
  rw [← neg_add]; unfold head; rw [← (head_sums h k).tsum_add (head_sums g k)]; congr 1
  apply tsum_congr; intro i; split_ifs <;> simp

omit [CompleteSpace V] in
lemma solution_scale (F : ℤ → V) (s : ℝ) (b k) : solution (s • F) b k=s • solution F b k := by
  unfold solution; split_ifs
  · unfold rest; rw [← tsum_const_smul'']; apply tsum_congr; intro i; split_ifs <;> simp
  unfold head; rw [smul_neg,← tsum_const_smul'']; congr 1
  apply tsum_congr; intro i; split_ifs <;> simp
lemma solution_sub {F G : ℤ → V} (h : Summable F) (g : Summable G) (b k) :
    solution (F-G) b k = solution F b k-solution G b k := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ G, solution_add h (show Summable ((-1:ℝ) • G) from g.const_smul (-1:ℝ)), solution_scale,neg_one_smul, sub_eq_add_neg]
omit [CompleteSpace V] [NormedSpace ℝ V] in
@[simp] lemma solution_zero (b k : ℤ) : solution (0: ℤ→V) b k=0 := by simp [solution,head,rest]

omit [CompleteSpace V] [NormedSpace ℝ V] in
lemma translate (b k u : ℤ) (F : ℤ → V) : solution (fun i => F (i-u)) (b+u) (k+u)=solution F b k := by
  unfold solution
  let e := Equiv.subRight u
  simp only [add_le_add_iff_right]; split
  · unfold rest; rw [← Equiv.tsum_eq e (fun i => if k < i then F i else 0)]
    apply tsum_congr; intro i; change _=if k < i-u then _ else _; split_ifs <;> first | rfl | omega
  unfold head; rw [← Equiv.tsum_eq e (fun i => if i≤k then F i else 0)]
  congr 1; apply tsum_congr; intro i; change _=if i-u≤k then _ else _; split_ifs <;> first | rfl | omega
end Ray
end YM.AnalyticNext.QuarticMatch.BoxChain
