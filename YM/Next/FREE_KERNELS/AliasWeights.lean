import Mathlib.Analysis.PSeries
import YM.Next.FREE_KERNELS.Aliases


/-!
Summable product weights over the mixed axes. No estimate of a
history-wide sum is to use dimension paid at block length `L`; these
constants cost before `L`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Finset
open scoped Topology BigOperators

variable {L : Side}

def up (l : Site L) (i : Axis) : ℝ := 1+ (lift l i).natAbs

def grade (l : Site L) : ℝ := 1+pdist l

def mix (l : Site L) := ∏ i, up l i

def decay (t : ℕ) (l : Site L) : ℝ := (mix l ^ t)⁻¹

lemma up_ge (l : Site L) (i : Axis) : 1 ≤ up l i := by unfold up; simp
lemma up_pos (l : Site L) (i : Axis) : 0 < up l i := one_pos.trans_le (up_ge ..)
lemma grade_ge (l : Site L) : 1 ≤ grade l := by unfold grade; simp
lemma grade_pos (l : Site L) : 0 < grade l := one_pos.trans_le (grade_ge ..)
lemma up_le (l : Site L) (i : Axis) : up l i ≤ grade l := by
  unfold up grade; exact add_le_add (le_refl _) (by exact_mod_cast component_le l i)
lemma hit_grade (l : Site L) : ∃ i, grade l=up l i := by
  obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_sup univ univ_nonempty fun i => (lift l i).natAbs
  exact ⟨i, by unfold grade up pdist; rw [he]⟩
lemma grade_gt {l : Site L} (h : l ≠ 0) : 1<grade l := by
  by_contra! hc
  apply h; apply lift_inj; funext i
  rw [lift_origin]; have he := (up_le l i).trans hc
  unfold up at he; simp_all

lemma grade_le_mix (l : Site L) : grade l ≤ mix l := by
  obtain ⟨k,hk⟩ := hit_grade l
  let f (i : Axis) := if i=k then (up l k) else 1
  have hb (i : Axis) : f i ≤ up l i := by unfold f; split <;> simp [*,up_ge l i]
  have hc (i : Axis) : 0 ≤ f i := by unfold f; split <;> simp [(up_pos l k).le]
  rw [hk,mix]
  calc
    _ = ∏ i, f i := by simp [f]
    _ ≤ _ := Finset.prod_le_prod (fun i _ => hc i) (fun i _ => hb i)
lemma mix_ge (l : Site L) : 1 ≤ mix l := (grade_ge _).trans (grade_le_mix l)
lemma mix_pos (l : Site L) : 0 < mix l := one_pos.trans_le (mix_ge l)
lemma decay_pos (l : Site L) (t : ℕ) : 0 < decay t l := by unfold decay; exact inv_pos.mpr (pow_pos (mix_pos _) _)
lemma decay_le_one (l : Site L) (t : ℕ) : decay t l ≤ 1 := by
  unfold decay; exact inv_le_one_of_one_le₀ (one_le_pow₀ (mix_ge l))
lemma decay_anti (l : Site L) : Antitone (fun i => decay i l) := by
  intro i j h
  unfold decay; exact inv_le_inv₀ (pow_pos (mix_pos _) _) (pow_pos (mix_pos _) _) |>.mpr (pow_le_pow_right₀ (mix_ge l) h)
lemma decay_add (l : Site L) (t r : ℕ) : decay (t+r) l=decay t l*decay r l := by
  simp [decay,pow_add,mul_comm]
lemma absorbs (l : Site L) (t r : ℕ) : grade l ^ t * decay (r+t) l ≤ decay r l := by
  rw [Nat.add_comm,decay_add, ← mul_assoc]
  refine (mul_le_mul_of_nonneg_right ?_ (decay_pos _ r).le).trans (le_of_eq (one_mul _))
  unfold decay
  rw [← div_eq_mul_inv, div_le_one (pow_pos (mix_pos l) _)]
  exact pow_le_pow_left₀ (grade_pos l).le (grade_le_mix l) t

private def priceAxis (x : ℤ) : ℝ := ((1+(x.natAbs:ℝ))^2)⁻¹
private lemma priceAxis_sum : Summable priceAxis := by
  unfold priceAxis
  have he := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow (p:=2) |>.mpr one_lt_two)
  rw [summable_int_iff_summable_nat_and_neg]; constructor <;> simpa [one_div,add_comm] using he

lemma decay_cost : ∃ C : ℝ, 0<C ∧ ∀ L : Side, (∑ i : Site L, decay 2 i) ≤ C := by
  let C := 1+∑' i, priceAxis i
  have hc (i : ℤ) : 0 ≤ priceAxis i := by unfold priceAxis; positivity
  have hC : 0<C := lt_of_lt_of_le one_pos (by unfold C; simp only [le_add_iff_nonneg_right]; exact tsum_nonneg hc)
  refine ⟨C^4, pow_pos hC _, fun L => ?_⟩
  have he (l : Site L) : decay 2 l=∏ i, priceAxis (lift l i) := by
    simp [decay,mix,up,priceAxis,Finset.prod_pow]
  have hf (L : Side) : Function.Injective (fun i : ZMod L.val => i.valMinAbs) := fun i j h => by
    simpa using congr_arg (fun z : ℤ => (z : ZMod L.val)) h
  have hb (L : Side) : (∑ i : ZMod L.val, priceAxis i.valMinAbs) ≤ C := calc
    _ = ∑ x ∈ univ.image ZMod.valMinAbs, priceAxis x := (Finset.sum_image ((hf L).injOn)).symm
    _ ≤ _ := (priceAxis_sum.sum_le_tsum _ fun i _ => hc i).trans (by unfold C; linarith)
  simp_rw [he]
  unfold lift Site Four
  rw [← Fintype.prod_sum (κ:= fun _ : Axis => Per L) (fun _ x => priceAxis (ZMod.valMinAbs x))]
  calc
    _ ≤ ∏ _ : Axis, C := Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => hc _) (fun _ _ => hb L)
    _ = _ := by simp [Axis]
end YM.Next.Free
