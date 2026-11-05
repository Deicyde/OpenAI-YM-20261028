import YM.Bid.Craft
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Newtown

set_option warningAsError false

/-!
# JsT near and far into JHs Promise

Periodized or on cover: the anchored growth from operator differences
at all cover y on the periodized lift is enough even without exact
alias zeroes or assumptions spending the seat stencil reserves on these
other charts. B70 Horizon.Deep application separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Newt
open Function Filter Finset Lattice Wilson RG Labels Laurent
open Pattern  
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Cover→E} {L r C M : ℝ}

def drift (b k : ℕ) (M r : ℝ) (p : Cover→E) := ∀ l : List Axis,l.length ≤ k → ∀ x,‖iterate p l x‖ ≤ M*r^(1+l.length)*(1+r*size x)^b

private lemma granule {b k j : ℕ} (hr : 0 ≤ r) (hM : 0 ≤ M) (h : drift b k M r p) (he : j < k) (x : Cover) :
    ‖piece j p (xyz x)‖ ≤ ((4*((j:ℝ)+1))^j*M) *r^(1+j) * (1+(size x:ℝ))^j := by
  refine (component j _ (show 0 ≤ M*r^(1+j) from mul_nonneg hM (by positivity)) (fun i hi => ?_) _).trans_eq (by ring)
  simpa [Laurent.size,hi] using h i (hi.trans_le he.le) 0

/-- Exact binomial pieces, true estimate both distance ranges. -/
lemma capital (b k : ℕ) (h : k ≤ b) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (M L : ℝ),1 ≤ L → 0 ≤ M → ∀ (p : Cover → E),
    drift b k M L⁻¹ p → ∀ x : Cover,
      (∀ i,i < k → ‖piece i p (xyz x)‖ ≤ C*M*L⁻¹^(1+i)*(1+(size x:ℝ))^b) ∧
      ‖tail k p x‖ ≤ C*M*L⁻¹^(1+k)*(1+(size x:ℝ))^b := by
  let c (i : ℕ) := (4*((i:ℝ)+1))^i
  let A : ℝ := (2:ℝ)^b
  have he i : 0 ≤ c i := by unfold c; positivity
  have ha : 1 ≤ A := one_le_pow₀ (by norm_num)
  let X := ∑ i∈Finset.range k, c i
  have hx : 0 ≤ X := sum_nonneg fun _ _ => he _
  let V := A+X
  have hv : 1 ≤ V := ha.trans (le_add_of_nonneg_right hx)
  refine ⟨V,hv,fun M L hL hM p hp x => ?_⟩
  let r := L⁻¹
  have hr : 0 < r := inv_pos.mpr (zero_lt_one.trans_le hL)
  have hr' : r ≤ 1 := inv_le_one_of_one_le₀ hL
  let y : ℝ := ↑(size x); let q := 1+y
  have hy : 0 ≤ y := Nat.cast_nonneg _; have hq : 1 ≤ q := by unfold q; linarith
  let w := M*r^(1+k)*q^b
  have hw : 0 ≤ w := mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hq) _)
  constructor
  · intro i hi; apply (granule hr.le hM hp hi _).trans
    change c i*M*r^_*q^_ ≤ _*M*r^_*q^_
    gcongr <;> first | exact hq | exact hi.le.trans h | exact le_trans (show c i ≤ X from single_le_sum (fun i _ => he i) (mem_range.mpr hi)) (le_add_of_nonneg_left (by positivity : 0 ≤ A))
  change ‖_‖ ≤ _*M*r^(1+k)*q^b
  have hT : V*M*r^(1+k)*q^b=V*w := by unfold w; ring
  rw [hT]
  rcases le_or_gt y L with h'|h'
  · apply (localized k (M:= A*M*r^(1+k)) (by positivity) L (fun l hl t ht => ?_) _ h').trans
    · change _* q^k ≤ _*w
      unfold w
      calc
        _ ≤ A*(M*r^(1+k)*q^b) := by rw [← mul_assoc,← mul_assoc]; gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hx) hw
    apply (hp l hl.le _).trans; rw [hl, mul_assoc A]
    rw [mul_comm _ ((1+L⁻¹*(size t:ℝ))^_)]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ b) (by positivity)
    rw [inv_mul_eq_div]; have H := div_le_one_of_le₀ ht (zero_le_one.trans hL); linarith
  have hu : 1 ≤ r*q := by
    unfold r; rw [one_le_inv_mul₀ (zero_lt_one.trans_le hL)]; unfold q; linarith
  have hz i (hi : i ≤ k) : r^(1+i)*q^i ≤ r^(1+k)*q^b := by
    calc
      _ = r*(r*q)^i := by rw [pow_add,mul_pow,pow_one]; ring
      _ ≤ r*(r*q)^k := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu hi) hr.le
      _ ≤ _ := by rw [mul_pow,←mul_assoc, pow_add,pow_one]; gcongr
  unfold tail Newt.take
  have ht : ‖p x‖ ≤ A*w := by
    refine (hp [] (by simp) x).trans ?_
    change M * r^(1+0)*(1+r*y)^b ≤ _
    unfold A w; simp only [add_zero,pow_one]
    calc
      _ ≤ M*r*(2*r*q)^b := by gcongr; unfold q; nlinarith only [hu,hr]
      _ = (2:ℝ)^b*(M*r^(1+b)*q^b) := by simp [mul_pow,pow_add,mul_assoc,mul_left_comm,mul_comm]
      _ ≤ _ := by gcongr (2:ℝ)^b*(M*?_ *q^b); exact pow_le_pow_of_le_one hr.le hr' (by omega)
  apply (norm_sub_le ..).trans; unfold V; rw [add_mul]; apply add_le_add ht
  rw [show X * w = ∑ i∈Finset.range k,c i*w from Finset.sum_mul ..]
  refine (norm_sum_le ..).trans (sum_le_sum (fun i hi => ?_)); have hj := mem_range.mp hi
  apply (granule hr.le hM hp hj _).trans
  change c i*M*r^_*q^_ ≤ c i * (M * r^_ * q^_)
  simp_rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hz i hj.le) hM) (he i)
end YM.MultiNext.SignedSource.Newt
