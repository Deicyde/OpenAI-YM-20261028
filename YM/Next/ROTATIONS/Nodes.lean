import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.LinearAlgebra.Lagrange
import YM.Compact.Borel
import YM.Mink.Geometry
import YM.OS.Flow
import YM.SNAG.Dense

/-! # Use tied high nodes in a scale band. -/
noncomputable section
namespace YM.Outer.Nodes
open Set Filter Function Polynomial
open scoped BigOperators
/-- node multipliers. Start at 2. -/
def num (j : ℕ) : ℝ := (j:ℝ)+2
def loc (j : ℕ) : ℝ := num j ^ 2
lemma num_ge (i : ℕ) : 2≤num i := by unfold num; simp
lemma num_pos (i) : 0<num i := lt_of_lt_of_le (by norm_num) (num_ge i)
lemma loc_pos (i) : 0<loc i := pow_pos (num_pos _) _
lemma loc_inj : Injective loc := by
  intro i j h
  have he := (sq_eq_sq₀ (num_pos i).le (num_pos j).le).mp h
  simpa [num] using he

def coeff (m j : ℕ) : Polynomial ℝ := Lagrange.basis (Finset.range m) loc j
private def interp (m : ℕ) := Lagrange.interpolate (Finset.range m) loc
lemma eval_interp (m) r x : Polynomial.eval x (interp m r)=∑ i∈Finset.range m, r i * (coeff m i).eval x := by
  rw [interp,Lagrange.interpolate_apply,eval_finsetSum]; unfold coeff; simp
lemma sums (m : ℕ) (j : ℕ) (h : j<m) (x : ℝ) :
    (∑ i∈Finset.range m,(coeff m i).eval x * (loc i)^j) = x^j := by
  simp_rw [mul_comm (_root_.Polynomial.eval x _)]; rw [← eval_interp m (fun i => (loc i)^j) x]
  -- interp_eq
  have hi : interp m (fun i => (loc i)^j)=X^j := by
    refine (Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.range m) loc_inj.injOn
      (Lagrange.degree_interpolate_lt _ loc_inj.injOn) ?_ (fun i hi => ?_))
    · simp [degree_pow,h]
    rw [interp,Lagrange.eval_interpolate_at_node _ loc_inj.injOn hi]; simp
  rw [hi]; simp

lemma remainder (m : ℕ) (x y : ℝ) (hy : 0≤y) (hx : x+y≠0) :
    (x+y)⁻¹ - ∑ i∈Finset.range m,(coeff m i).eval x * (loc i+y)⁻¹ =
        (x+y)⁻¹ * ∏ i∈Finset.range m, ((loc i-x)/(loc i+y)) := by
  let T := Finset.range m
  let I := interp m (fun i => (loc i+y)⁻¹)
  let A : Polynomial ℝ := 1 - (X+C y)*I
  let n := Lagrange.nodal T loc
  have hi (i : ℕ) : 0 < loc i+y := add_pos_of_pos_of_nonneg (loc_pos _) hy
  have hz : ∀ i∈T, -y≠loc i := by intro i _ ha; linarith [hi i]
  have hu : n.eval (-y)≠0 := Lagrange.eval_nodal_not_at_node hz
  let B := n*C ((n.eval (-y))⁻¹)
  classical
  let s := insert (-y) (T.image loc)
  have hh : s.card=T.card+1 := by
    unfold s; rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn loc_inj.injOn]
    intro h; obtain ⟨i,ht,hx⟩ := Finset.mem_image.mp h; exact hz i ht hx.symm
  have hd (p : Polynomial ℝ) (h : p.degree ≤ ↑T.card) : p.degree < s.card := by rw [hh]; apply h.trans_lt; exact_mod_cast Nat.lt_succ_self _
  have hb := Lagrange.degree_nodal (R:=ℝ) (s:=T) (v:=loc)
  have he : A=B := by
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq s (hd _ ?_) (hd _ ?_) ?_
    · have hI : I.degree < ↑T.card := Lagrange.degree_interpolate_lt _ loc_inj.injOn
      refine (degree_sub_le _ _).trans (max_le ?_ ?_)
      · simp
      refine (degree_mul_le _ _).trans ?_
      have he : (X+C y).degree=(1:WithBot ℕ) := by simp
      rw [he]
      rcases eq_or_ne I 0 with h|h
      · simp [h]
      rw [degree_eq_natDegree h] at hI ⊢
      have he : I.natDegree<T.card := by exact_mod_cast hI
      exact_mod_cast (show 1+I.natDegree ≤ T.card by omega)
    · exact (degree_mul_le _ _).trans (by rw [show n.degree=↑T.card from hb]; exact (add_le_add_right degree_C_le (↑T.card:WithBot ℕ)).trans_eq (add_zero _))
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|h
    · simp [A,B,hu]
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    have hv : I.eval (loc j)=(loc j+y)⁻¹ := Lagrange.eval_interpolate_at_node _ loc_inj.injOn hj
    simp [A,B,hv,(hi j).ne',show n.eval (loc j)=0 from Lagrange.eval_nodal_at_node hj]
  have he := congr_arg (Polynomial.eval x) he
  simp only [A,B,eval_sub,eval_one,eval_mul,eval_add,eval_C,eval_X,n,Lagrange.eval_nodal] at he
  have hh : ((∏ i∈T,(x-loc i))*((∏ i∈T,(-y-loc i)))⁻¹) = ∏ i∈T,(loc i-x)/(loc i+y) := by
    rw [← div_eq_mul_inv,← Finset.prod_div_distrib]; refine Finset.prod_congr rfl ?_
    intro i _; rw [neg_sub_left,← neg_sub x (loc i),div_neg,neg_div]
  change _ - Finset.sum T _ = _ * Finset.prod T _
  rw [hh] at he
  simp_rw [mul_comm (_root_.Polynomial.eval x _)]
  rw [show Finset.sum T _ = I.eval x from (eval_interp m _ _).symm,← he]; field_simp
def kernel (m : ℕ) (e p E : ℝ) := ∏ i∈Finset.range m, (((e*num i)^2-p^2)/((e*num i)^2+E^2))
lemma scaled_interp (m : ℕ) (p E a : ℝ) (h : 0<E) (ha : a≠0) :
    (p^2+E^2)⁻¹-∑ i∈Finset.range m,(coeff m i).eval ((p/a)^2) * ((a*num i)^2+E^2)⁻¹ = (p^2+E^2)⁻¹ * kernel m a p E := by
  let x := (p/a)^2; let y := (E/a)^2
  have hy : 0 < y := by unfold y; exact sq_pos_of_ne_zero (by positivity)
  have hh := remainder m x y hy.le (show x+y≠0 by unfold x; positivity)
  have hi (i) : a^2*(loc i+y) = (a*num i)^2 + E^2 := by dsimp only [loc,y]; field_simp
  have hc : a^2*(x+y) = p^2+E^2 := by dsimp only [x,y]; field_simp
  change _ - ∑ i∈Finset.range m,(coeff m i).eval x * _= _
  have ht : kernel m a p E=∏ i∈Finset.range m,(loc i-x)/(loc i+y) := by
    unfold kernel; apply Finset.prod_congr rfl; intro i _
    have H : (a*num i)^2-p^2 = a^2*(loc i-x) := by dsimp only [loc,x]; field_simp
    rw [H,← hi,mul_div_mul_left _ _ (pow_ne_zero _ ha)]
  rw [ht,← hc]; simp_rw [← hi,mul_inv]
  calc
    _ = (a^2)⁻¹*((x+y)⁻¹ - ∑ i∈Finset.range m,(coeff m i).eval x * (loc i+y)⁻¹) := by
      rw [mul_sub,Finset.mul_sum]; congr 1
      refine Finset.sum_congr rfl fun i _ => mul_left_comm ..
    _ = _ := by rw [hh,mul_assoc]
end YM.Outer.Nodes
